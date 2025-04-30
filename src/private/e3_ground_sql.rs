// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use crate::ast::{QualIdentifier, SpecConstant, Symbol};
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::{TableAlias, Column};
use crate::private::z_utilities::OptionMap;


////////////////////// Data structures for grounding queries //////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Mapping (pub SQLExpr, pub Column);


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Value(Column, Ids),
    G(TableAlias),
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    Predefined(Predefined, Box<Vec<SQLExpr>>),
}

#[derive(Debug, strum_macros::Display, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Predefined {
    // display is the SMT-lib symbol

    #[strum(to_string = "and")] And,
    #[strum(to_string = "or" )] Or,
    #[strum(to_string = "not")] Not,
    // "=>" is replaced by a disjunction during annotation
    #[strum(to_string = "="  )] BoolEq(bool),
    #[strum(to_string = "="  )] Eq,
    #[strum(to_string = "<"  )] Less,
    #[strum(to_string = "<=" )] LE,
    #[strum(to_string = ">=" )] GE,
    #[strum(to_string = ">"  )] Greater,
    #[strum(to_string = "distinct")] Distinct,
    #[strum(to_string = "ite")] Ite,

    #[strum(to_string = "+"  )] Plus,
    #[strum(to_string = "-"  )] Minus,
    #[strum(to_string = "*"  )] Times,
    #[strum(to_string = "div")] Div,
    #[strum(to_string = "mod")] Mod,
    #[strum(to_string = "abs")] Abs,
}

enum Associativity {
    Unary,
    Binary,
    Associative,
    Chainable,
    Pairwise,
    LeftAssoc,
    Ite
}

fn associativity(function: &Predefined) -> Associativity {
    match function {
        Predefined::And       => Associativity::Associative,
        Predefined::Or        => Associativity::Associative,
        Predefined::Not       => Associativity::Unary,
        Predefined::BoolEq(_) => Associativity::Chainable,
        Predefined::Eq        => Associativity::Chainable,
        Predefined::Less      => Associativity::Chainable,
        Predefined::LE        => Associativity::Chainable,
        Predefined::GE        => Associativity::Chainable,
        Predefined::Greater   => Associativity::Chainable,
        Predefined::Distinct  => Associativity::Pairwise,
        Predefined::Ite       => Associativity::Ite,
        Predefined::Plus      => Associativity::LeftAssoc,
        Predefined::Minus     => Associativity::LeftAssoc,
        Predefined::Times     => Associativity::LeftAssoc,
        Predefined::Div       => Associativity::LeftAssoc,
        Predefined::Mod       => Associativity::Binary,
        Predefined::Abs       => Associativity::Unary,
    }
}


///////////////////////////  Display //////////////////////////////////////////


impl Mapping {

    pub(crate) fn to_if(
        &self,
        variables: &OptionMap<Symbol, Column>
    ) -> Option<String> {
        let (exp, ids) = self.0.to_sql(variables);
        let col = self.1.to_string();
        if exp == col {
            None
        } else {
            match ids {
                Ids::All => None,
                Ids::Some => Some(format!("if_({}, {})", exp, col)),  // is_id(exp) or exp = col
                Ids::None => Some(format!("apply(\"=\",{}, {})", exp, col))
            }
        }
    }

    pub(crate) fn to_join(
        &self,
        variables: &OptionMap<Symbol, Column>
    ) -> Option<String> {
        let (exp, ids) = self.0.to_sql(variables);
        let col = self.1.to_string();
        if exp == col {
            None
        } else {
            match ids {
                Ids::All => Some(format!("{} = {}", exp, col)),
                Ids::Some => Some(format!("join_({}, {})", exp, col)),  // NOT is_id(exp) or exp = col
                Ids::None => {
                    // LINK src/doc.md#_Variables
                    if let SQLExpr::Variable(_) = self.0 {  // an infinite variable mapped to an interpretation
                        // Variable + Ids::None describe an infinite variable
                        Some(format!("{exp} = {col}"))
                    } else {
                        None
                    }
                }
            }
        }
    }
}


impl SQLExpr {
    // it can return an empty string !
    pub(crate) fn to_sql(
        &self,
        variables: &OptionMap<Symbol, Column>
    ) -> (String, Ids) {

        match self {
            SQLExpr::Boolean(value) => (format!("\"{value}\""), Ids::All),

            SQLExpr::Constant(spec_constant) => {
                match spec_constant {
                    SpecConstant::Numeral(s) => (format!("{s}"), Ids::All),
                    SpecConstant::Decimal(s) => (format!("{s}"), Ids::All),
                    SpecConstant::Hexadecimal(s) => (format!("\"{s}\""), Ids::All),
                    SpecConstant::Binary(s) => (format!("\"{s}\""), Ids::All),
                    SpecConstant::String(s) => (format!("\"{s}\""), Ids::All),
                }
            },
            SQLExpr::Variable(symbol) => {
                // LINK src/doc.md#_Variables
                let column = variables.get(symbol).unwrap();
                if let Some(column) = column {
                    (column.to_string(), Ids::All)
                } else {
                    (format!("\"{symbol}\""), Ids::None)
                }
            },
            SQLExpr::Value(column, ids) => (column.to_string(), ids.clone()),
            SQLExpr::Apply(qual_identifier, exprs) =>
                sql_for("apply", qual_identifier.to_string(), exprs, variables),
            SQLExpr::G(table_alias) => (format!("{table_alias}.G"), Ids::None),
            SQLExpr::Construct(qual_identifier, exprs) => {
                // LINK src/doc.md#_Constructor
                sql_for("construct2", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Predefined(function, exprs) => {
                match associativity(function) {
                    Associativity::Unary => {
                        // NOT, abs
                        let e = exprs.first().unwrap();
                        let (expr, ids) = e.to_sql(variables);
                        if ids == Ids::None {
                            (format!("apply(\"{function}\", {expr})"), Ids::None)
                        } else if *function == Predefined::Not {
                            (format!("not_({expr})"), ids)
                        } else {
                            (format!("abs_({expr})"), ids)
                        }
                    },
                    Associativity::Binary => {
                        // mod

                        let mut ids = Ids::All;
                        let terms = exprs.iter()
                            .map(|e| {
                                let (e, ids_) = e.to_sql(variables);
                                ids = max(ids.clone(), ids_.clone());
                                e
                            }).collect::<Vec<_>>();

                        if let [a, b] = &terms[..] {
                            if ids == Ids::None {
                                (format!("apply(\"{function}\", {a}, {b})"),
                                ids.clone())
                            } else {
                                (format!("left_(\"{function}\", {a}, {b})"),
                                ids.clone())
                            }
                        } else {
                            panic!("incorrect number of arguments for mod")
                        }
                    },
                    Associativity::Associative => {
                        // AND, OR
                        let name = function.to_string();
                        let mut ids = Ids::All;
                        let exprs =
                            exprs.iter().cloned().filter_map( |e| {
                                let (e_, ids_) = e.to_sql(variables);
                                ids = max(ids.clone(), ids_.clone());
                                // try to simplify
                                match e {
                                    SQLExpr::Boolean(b) =>
                                        if name == "and" && b { None }
                                        else if name == "or" && !b { None }
                                        else { Some(e_) },
                                    _ => Some(e_)
                                }
                            }).collect::<Vec<String>>();
                        if exprs.len() == 0 {
                            if name == "and" {
                                ("\"true\"".to_string(), Ids::All)
                            } else {
                                ("\"false\"".to_string(), Ids::All)
                            }
                        } else if exprs.len() == 1 {
                            (exprs.first().unwrap().clone(), ids)
                        } else {
                            if ids == Ids::None {
                                (format!("apply(\"{name}\", {})", exprs.join(", ")), ids)
                            } else {
                                (format!("{name}_({})", exprs.join(", ")), ids)
                            }
                        }
                    },
                    Associativity::Chainable => {
                        // LINK src/doc.md#_Equality
                        // Eq, comparisons

                        let (terms, ids) = collect_args(Ids::All, exprs, variables);

                        // simplify
                        match function {
                            Predefined::Eq => {
                                let equal = exprs.iter().zip(exprs.iter().skip(1))
                                        .all(|(a, b)| *a == *b);
                                if equal {
                                    return ("\"true\"".to_string(), Ids::All)
                                }
                            }
                            _ => {}
                        }

                        if ids == Ids::None && !matches!(*function, Predefined::BoolEq(_)) {
                            (format!("apply(\"{function}\", {terms})"), ids)
                        } else {
                            match function {
                                Predefined::BoolEq(default)    => (format!("bool_eq_(\"{default}\", {terms})"), ids),
                                Predefined::Eq        => (format!("eq_({terms})"), ids),
                                Predefined::Less
                                | Predefined::LE
                                | Predefined::GE
                                | Predefined::Greater => (format!("compare_(\"{function}\", {terms})"), ids),
                                _ => unreachable!()
                            }
                        }
                    },
                    Associativity::Pairwise => { // distinct

                        let (terms, ids) = collect_args(Ids::All, exprs, variables);

                        if ids == Ids::None {
                            (format!("apply(\"distinct\", {terms})"), ids)
                        } else {
                            (format!("compare_(\"distinct\", {terms})"), ids)
                        }
                    },
                    Associativity::LeftAssoc => {
                        // + - * div

                        let (terms, ids) = collect_args(Ids::All, exprs, variables);

                        if ids == Ids::None {
                            (format!("apply(\"{function}\", {terms})"), ids)
                        } else {
                            (format!("left_(\"{function}\", {terms})"), ids)
                        }
                    },
                    Associativity::Ite => {
                        let mut ids = Ids::All;
                        let terms = exprs.iter()
                            .map(|e| {
                                let (e, ids_) = e.to_sql(variables);
                                ids = max(ids.clone(), ids_.clone());
                                e
                            }).collect::<Vec<_>>();

                        if terms[1] == terms[2] {  // condition is irrelevant
                            (terms[1].clone(), ids.clone())
                        } else if terms[0] == "\"true\"" {
                            (terms[1].clone(), ids.clone())
                        } else if terms[1] == "\"false\"" {
                            (terms[2].clone(), ids.clone())
                        } else {
                            let terms = terms.join(", ");
                            if ids == Ids::None {
                                (format!("apply(\"{function}\", {terms})"), ids.clone())
                            } else {
                                (format!("ite_({terms})"), ids.clone())
                            }
                        }
                    },
                }
            }
        }
    }
}



/// Use either "apply" or "construct2", according to the first argument.
/// See description of these functions in y_db module.
///
/// Arguments:
/// * application: either "apply" or "construct2"
fn sql_for(
    application: &str,
    function: String,
    exprs: &Box<Vec<SQLExpr>>,
    variables: &OptionMap<Symbol, Column>,
) -> (String, Ids) {
    let ids =
        if application == "construct2" {
            Ids::All
        } else {
            Ids::None
        };
    if exprs.len() == 0 {
        (format!("\"{function}\""), ids)
    } else {
        let (terms, ids) = collect_args(ids, exprs, variables);
        (format!("{application}(\"{function}\", {terms})"), ids)
    }
}

/// converts each exprs to a string, join them by ", ", and determines Ids for the result
fn collect_args(
    ids: Ids,
    exprs: &Box<Vec<SQLExpr>>,
    variables: &OptionMap<Symbol, Column>
) -> (String, Ids) {
    let mut ids = ids;
    let terms = exprs.iter()
        .map(|e| {
            let (e, ids_) = e.to_sql(variables);
            ids = max(ids.clone(), ids_.clone());
            e
        })
        .collect::<Vec<_>>().join(", ");
    (terms, ids)
}