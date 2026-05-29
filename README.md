# sporadic_srg_120-56-28-24
Code to study a sporadic strongly regular graph with parameters (120,56,28,24), as basis of the manuscript "The sporadic primitive vertex-transitive strongly regular graph with parameters $(120,56,28,24)$" by Sam Adriaensen, Robert Bailey, Jan De Beule and Morgan Rodgers.

The code consists of several parts. 

In the part "SPREADS" we consider that hyperbolic quadric Q+(7,2) and we construct a spread and an ovoid of this polar space using the coclique finder of grape. We compute the stabilizer group G of one system of generators. We then compute the orbit of the chosen spread under the subgroup of G stabilising two points of the ovoid, and pick the orbit of spreads of size 120. Then we check that G acts generously transitive on the spreads. This leads to a proof of Proposition 3.2 of the paper. 

Now we are ready to study the orbitals of G and to set up the association scheme. The eventual objective is to merge relations so that we get the desired strongly regular graph. To decide which relations to be merged, we use the matrix of eigenvalues of the scheme. 

Finally, we check that the resulting graph is the graph we want to construct using the hyperbolic quadric, i.e. with the right parameters and automorphism group S7. 

In the part "OVOIDS" we aim to prove Theorem 4.3 of the paper. This theorem yields another merge of relations into the desired srg.  

In the final part "COCLIQES" we investigate the cocliques of the desired srg and compare the size of the cocliques with Hoffman's ratio bound.
