// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;

use crate::api::Symbol;


/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct View {
    // for variable x in Color --> select color.G as x, color.G as G from Color
    //      variables:  `x -> Color.G`, i.e., variable name to column name
    //      condition:  ""
    //      grounding:  "Color.G"
    //      joins:      Color
    //      where:      ""
    //      group_by:   ""
    //      _ids:    true

    // For a calculated term p
    // e.g., p(x, f(a)) --> select color.G as x, apply("p", Color.G, apply("f", "a")) as G from Color
    //      variables:  `x -> Color.G`, i.e., variable name to column name
    //      condition:  ""
    //      grounding:  apply("p", Color.G, apply("f", "a"))
    //      joins:      Color
    //      where:      ""
    //      group_by:   ""
    //      _ids:    false

    // for a tabled term: 2 options (create a view or not)
    // e.g., p(x, a) -->
    //      create view term_2 as
    //          select p.a1 as x,
    //                 .. as cond,
    //                 p.G as G
    //            from p
    //           where p.a2 = "a"
    //
    //      variables: `x -> p.a1`, i.e., variable name to column name
    //      condition: ""
    //      grounding: "p.G"
    //      joins: "p"
    //      where: "p.a2 = "a""
    //      view:

    pub(crate) variables: IndexMap<Symbol, String>,
    pub(crate) condition: String,
    pub(crate) grounding: String,
    pub(crate) joins: IndexMap<String, String>,
    pub(crate) where_: String,
    pub(crate) group_by: String,

    pub(crate) _ids: Ids,
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Ids { All, _Some, None }

impl std::fmt::Display for View {

    // select {variables.0} as {variables.1},
    //        {condition} as cond,  -- if condition
    //        {grounding} as G,
    //   from {joins[0].key}
    //   join {joins[i].key} on {joins[i].value}
    //  where {condition}
    // group by {variables.0}, {grounding}  -- if condition

    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let variables = self.variables.iter()
            .map(|(k, v)| format!("{v} AS {k}"))
            .collect::<Vec<_>>()
            .join(", ");
        let condition = if &self.condition == "" { "".to_string()
            } else if variables != "" {
                format!(", {0} as cond", &self.condition)
            } else {
                format!("{0} as cond", &self.condition)
            };
        let grounding = if variables != "" || condition != "" {
                format!(", {}", &self.grounding)
            } else {
                self.grounding.to_string()
            };
        let tables = self.joins.iter()
            .map(|(table, on)| if on == "" { table.to_string() } else {
                format!("{table} ON {on}")
            })
            .collect::<Vec<_>>()
            .join(" JOIN ");
        let tables = if tables != "" {
                format!(" FROM {tables}")
            } else { "".to_string() };
        let where_ = if self.where_ == "" { "".to_string() } else {
            format!(" WHERE {0}", self.where_)
        };
        let group_by = if self.group_by == "" { "".to_string() } else {
            format!(" GROUP BY {0}", self.group_by)
        };
        write!(f, "SELECT {variables}{condition}{grounding} AS G{tables}{where_}{group_by}")
    }
}

