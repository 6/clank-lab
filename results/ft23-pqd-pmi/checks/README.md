# Further credits

Alfred Müller and Marco Scarsini's [Archimedean copulae and positive dependence](https://doi.org/10.1016/j.jmva.2004.04.003), Theorem 2.7 in its [2003 working version](https://www.bemservizi.unito.it/repec/icr/wp2003/Scarsini25-03.pdf), gives the superadditivity criterion for positive lower orthant dependence, attributed there to Joe, *Multivariate Models and Dependence Concepts* (1997), page 109. In two dimensions this is PQD. The proof here verifies the needed superadditivity inequality directly for the displayed generator.

Juan Fernández Sánchez and Wolfgang Trutschnig's [Singularity aspects of Archimedean copulas](https://doi.org/10.1016/j.jmaa.2015.06.036), Corollary 4 in the [June 22, 2015 preprint](https://www.trutschnig.net/p21.pdf), expresses the mass on a level curve using one-sided generator derivatives. That structural observation informed the use of a generator with a corner. The present proof evaluates rectangle increments directly and does not require their mass formula as an assumption.

Sebastian Fuchs and Marco Tschimpke's earlier [Total positivity of copulas from a Markov kernel perspective](https://arxiv.org/abs/2205.01914), Theorem 4.6, studies different positive-dependence properties through one-sided derivatives. It supplies related context; the conjecture answered here is Conjecture 1 of their later paper cited in the main README.

The complete check is the Lake project in [lean/](../lean/). No separate numerical checker is needed to reproduce the theorem.
