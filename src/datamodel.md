Below is a copy of a selection of the `struct` and `enum` declarations.

```
pub struct Solver {
    pub(crate) backend: Backend,
    pub conn: Connection,
    pub(crate) parametric_sorts: IndexMap<Symbol, ParametricObject>,
    pub(crate) sorts: IndexMap<Sort, SortObject>,
    pub(crate) functions: IndexMap<QualIdentifier, FunctionObject>,
    // pub(crate) qualified_functions: IndexMap<QualIdentifier, FunctionObject>,
    pub(crate) assertions_to_ground: Vec<(String, Term)>,
    pub(crate) groundings: IndexMap<Term, Grounding>,
}
pub(crate) enum ParametricObject {
    Datatype(DatatypeDec),
    DTDefinition{ variables: Vec<Symbol>, definiendum: Sort },
    Recursive,
    Unknown
}
pub(crate) enum SortObject{
    Normal{datatype_dec: DatatypeDec, table: TableName, row_count: usize},
    Recursive,
    Infinite,
    Unknown
}
pub(crate) enum FunctionObject {
    Predefined{boolean: Option<bool>},
    Constructor,
    NotInterpreted{signature: (Vec<Sort>, Sort, bool)},
    NonBooleanInterpreted{ table_g: Interpretation},
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
        grounding: Either<SQLExpr, (TableAlias, Ids)>,
        exclude: Option<bool>,
        query: GroundingQuery,
        ids: Ids,
    },
}
pub(crate) enum GroundingQuery {
    Join {
        variables: OptionMap<Symbol, Column>,
        conditions: Vec<Either<Mapping, TableAlias>>,
        grounding: SQLExpr,
        natural_joins: IndexSet<NaturalJoin>,
        theta_joins: IndexSet<ThetaJoin>,
        precise: bool,
    },
    Aggregate {
        agg: String,
        free_variables: OptionMap<Symbol, TableAlias>,
        infinite_variables: Vec<SortedVar>,
        sub_view: Box<GroundingView>,
    },
    Union {
        sub_queries: Box<Vec<GroundingQuery>>,
        precise: bool
    }
}
pub(crate) enum NaturalJoin {
    Variable(TableAlias, Symbol),
    ViewType(GroundingQuery, TableAlias, Vec<Symbol>),
}
pub(crate) type ThetaJoin = (TableAlias, Vec<Mapping>);
pub(crate) struct Mapping (pub SQLExpr, pub Column);
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Value(Column, Ids),
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),
    Predefined(Predefined, Box<Vec<SQLExpr>>),
}
```
