All the pieces of code that implement a particular functionality are marked with

```
// LINK src/doc.md#<topic>
```

For example, // LINK src/doc.md#_Equality

The documented topics are listed below:

## // LINK src/doc.md#_Equality

The G grounding of a (chained) equality $t_0=t_1\ldots=t_i$ is $\prod_{\bar x| (\bigwedge_i \underline{t_i^G})  | \bigwedge_i t_i=t_{i+1}} (\bowtie_i t_i^G )$.

The TU grounding of an equality is $\prod_{\bar x| (\bigwedge_i \underline{t_i^G})  | \bigwedge_i t_i=t_{i+1}} (\bowtie_{\bigwedge_i \rho_i} t_i^G )$ where $\rho_i = \lnot \text{is\_id}(t_i) \lor \lnot \text{is\_id}(t_i) \lor t_i=t_{i+1}$.

The UF grounding of equality is $\prod_{\bar x| (\bigwedge_i \underline{t_i^G})  | \bigwedge_i t_i=t_{i+1}} (\bowtie_{\bigwedge_i \rho_i} t_i^G )$ where $\rho_i = \lnot \text{is\_id}(t_i) \lor \lnot \text{is\_id}(t_i) \lor t_i \neq t_{i+1}$.

The where clause in a JOIN query for a predefined operator (e.g. or) is $\bigcup_i \lnot \text{is\_id}(t_i) \lor G*$, where $G*$ is the grounding in SQL form without $\text{is\_id}$, negated (for UF).

So, all predefined SQLExpr operators can be shown in 3 ways:

* as an $\text{eq\_}$ formula in a grounding (with simplification when $\text{is\_id}(t_i)$)
* as an SQL theta condition (with $\lnot \text{is\_id}(t_i)$, and possibly negated)
* as an SQL formula without is_id
