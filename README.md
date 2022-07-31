# Partitions of the Negative Parts of Vertices of Hypercube Graphs, and Vertex Decompositions w.r.t. Distinguished Symmetric Cycles #

A Haskell nodule exporting five functions that implement enumeration
mechanisms described in Theorem 6.4 from the 
monograph [A.O. Matveev, Symmetric Cycles](https://www.jennystanford.com/), 
Jenny Stanford Publishing, 2023, and illustrated in Example 6.5.

Let $t$ be an integer, $t\geq 3$. We denote by $[t]$ the *ground set* $\langle 1,2,\ldots, t\rangle$.
Given *odd* integers $\ell',\ell'',\ell\in [t]$, 
and positive integers $j'$ and $j''$, we are interested in statistics 
related to the following family of *ordered pairs* $(A,B)$ 
of disjoint *unordered subsets* $A$ and $B$ of the ground set $[t]$:

$\langle(A,B) \in 2^{[t]} \times 2^{[t]}: |A\cap B|=0, 0<|A|=j', 0<|B|=j'', j'+j''<t, \mathfrak{q}(A)=\ell', \mathfrak{q}(B)=\ell'', \mathfrak{q}(A\dot\cup B)=\ell\rangle$.

Here the quantity $\mathfrak{q}(A):=|\boldsymbol{Q}({}_{-A}\mathrm{T}^{(+)},\boldsymbol{R})|$ 
means the size of the decomposition set of the vertex, whose negative part is
$A$, w.r.t. the distinguished symmetric cycle $\boldsymbol{R}$; see a 
[note](https://github.com/andreyomatveev/distinguished-symmetric-cycles/blob/main/Matveev-DistinguishedSymmetricCycles-2022-07-13.pdf) 
in the [distinguished-symmetric-cycles](https://github.com/andreyomatveev/distinguished-symmetric-cycles) repository.
