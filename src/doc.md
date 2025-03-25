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
