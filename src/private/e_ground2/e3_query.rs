
/// Contains what is needed to construct the grounding query of a term, in a composable way.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum GroundingQuery {
    Todo(String)
    // Join {
    //     /// maps variables to None if its domain is infinite or to a Column in a Type or Interpretation table.
    //     variables: OptionMap<Symbol, Column>,
    //     conditions: Vec<Either<Mapping, Option<TableAlias>>>,  // vector of mapping or `if_` column of a table. If TableAlias is None, "true".
    //     grounding: SQLExpr,
    //     outer: Option<bool>,  // the default boolean value for outer joins (None for inner join)
    //     natural_joins: IndexSet<NaturalJoin>,  // cross-products with sort, or joins with grounding sub-queries
    //     theta_joins: IndexMap<TableAlias, Vec<Option<Mapping>>>,  // joins with interpretation tables
    //     wheres: Vec<Rho>,  // set of equality conditions

    //     has_g_complexity: bool,  // LINK src/doc.md#_has_g_complexity
    // },
    // Aggregate {
    //     agg: String,  // "" (top-level), "and" or "or"
    //     free_variables: OptionMap<Symbol, TableAlias>,  // None for infinite variables
    //     infinite_variables: Vec<SortedVar>,
    //     default: Option<bool>,  // to generate Y cross-product
    //     sub_view: Box<GroundingView>,  // the sub_view has more variables than free_variables

    //     has_g_complexity: bool,  // LINK src/doc.md#_has_g_complexity
    // },
    // Union {
    //     sub_queries: Box<Vec<GroundingQuery>>,  // the sub-queries are Join and have the same columns

    //     has_g_complexity: bool,  // LINK src/doc.md#_has_g_complexity
    // }
}


/// A flag indicating whether the values in an inetrpretation table are all Ids, some Ids, or all unknown.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Ids {
    All, // lowest
    Some,
    None // highest
}

impl GroundingQuery {

    pub(crate) fn to_sql(
        &self,
        indent: &str
    ) -> String {
        match self {
            GroundingQuery::Todo(msg) => format!("{indent}{msg}")
        }
    }
}