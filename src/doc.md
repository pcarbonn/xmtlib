# Datamodel

Below is a copy of a selection of the `struct` and `enum` declarations.

```

pub struct Solver {
    pub(crate) backend: Backend,
    pub conn: Connection,
    pub(crate) polymorphic_sorts: IndexMap<Symbol, PolymorphicObject>,
    pub(crate) canonical_sorts: IndexMap<Sort, CanonicalSort>,
    pub(crate) sort_objects: IndexMap<CanonicalSort, SortObject>,
    pub(crate) interpretable_functions: IndexMap<L<Identifier>, (Vec<CanonicalSort>, CanonicalSort)>,
    pub(crate) function_objects: IndexMap<(L<Identifier>, Vec<CanonicalSort>),
				     IndexMap<CanonicalSort, FunctionObject>>,
    pub(crate) assertions_to_ground: Vec<L<Term>>,
    pub(crate) groundings: IndexMap<(L<Term>, bool), (Grounding, CanonicalSort)>,
    pub(crate) grounded: IndexSet<Identifier>,
    pub(crate) converted: IndexSet<L<Identifier>>,
    pub(crate) db_names: IndexSet<String>,
}
pub(crate) enum PolymorphicObject {
    SortDefinition{ variables: Vec<Symbol>, definiendum: Sort },
    Datatype(DatatypeDec),
    RecursiveDT(DatatypeDec),
    Unknown
}
pub(crate) enum SortObject{
    Normal{datatype_dec: DatatypeDec, table: TableName, row_count: usize},
    Recursive,
    Infinite,
    Unknown
}
pub(crate) enum FunctionObject {
    Predefined{function: Predefined, boolean: Option<bool>},
    Constructor,
    NotInterpreted,
    Interpreted(Interpretation),
    BooleanInterpreted{table_tu: Interpretation, table_uf: Interpretation, table_g: Interpretation}
}
pub(crate) enum Interpretation {
    Table{name: TableName, ids: Ids},
    Infinite
}
pub(crate) enum Grounding {
    NonBoolean(GroundingView),
    Boolean{tu: GroundingView, uf: GroundingView, g: GroundingView}
}
pub(crate) enum GroundingView {
    Empty,
    View {
        free_variables: OptionMap<Symbol, TableAlias>,
        condition: bool,
        grounding: Either<SQLExpr, TableAlias>,
        exclude: Option<bool>,
        query: GroundingQuery,
        ids: Ids,
        to_be_defined: IndexSet<L<Identifier>>
    },
}
pub(crate) enum GroundingQuery {
    Join {
        variables: OptionMap<Symbol, Column>,
        conditions: Vec<Either<Mapping, TableAlias>>,
        grounding: SQLExpr,
        outer: Option<bool>,
        natural_joins: IndexSet<NaturalJoin>,
        theta_joins: IndexMap<TableAlias, Vec<Option<Mapping>>>,
        wheres: Vec<Rho>,
        has_g_complexity: bool,
    },
    Aggregate {
        agg: String,
        free_variables: OptionMap<Symbol, TableAlias>,
        infinite_variables: Vec<SortedVar>,
        default: Option<bool>,
        sub_view: Box<GroundingView>,
        has_g_complexity: bool,
    },
    Union {
        sub_queries: Box<Vec<GroundingQuery>>,
        has_g_complexity: bool
    }
}
pub(crate) enum NaturalJoin {
    CrossProduct(TableAlias, Symbol),
    ViewJoin(GroundingQuery, TableAlias, Vec<Symbol>),
}
pub(crate) struct Mapping (pub SQLExpr, pub Column);
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Value(Column, Ids),
    G(TableAlias),
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),
    Predefined(Predefined, Box<Vec<SQLExpr>>),
}
```

# Topics

All the pieces of code that implement a particular functionality are marked with

```
// LINK src/doc.md#<topic>
```

For example, // LINK src/doc.md#_Equality

The links can be followed on VSCode using [Comment Anchors](https://marketplace.visualstudio.com/items?itemName=ExodiusStudios.comment-anchors).

The documented topics are listed below:

## // LINK src/doc.md#_Variables

## // LINK src/doc.md#_Equality

## // LINK src/doc.md#_Infinite

## // LINK src/doc.md#_Constructor

# // LINK src/doc.md#_has_g_complexity

A query has G complexity if it generates (before filtering by a where clause) as many rows as the cross-product of its free variable.
Hence:

* a finite G view has G complexity
* any query over an infinite domain does not have G complexity
* the TU query for a compound term for a predicate with a truncated interpretation does not have G complexity.
* an equality or comparison has G complexity.

# // LINK src/doc.md#_exclude

A G view never has an exclude.
A TU or UF view has an exclude iff its query has G complexity.
The exclude is not added to the sql if the G column is true (or false).
