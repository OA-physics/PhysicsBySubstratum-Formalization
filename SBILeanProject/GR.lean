import SBILeanProject.GR.ConstraintCapacity
import SBILeanProject.GR.ReachabilityBoundary
import SBILeanProject.GR.MetricClosure
import SBILeanProject.GR.InertialPersistence
import SBILeanProject.GR.CausalPropagation
import SBILeanProject.GR.InertialSymmetry
import SBILeanProject.GR.LorentzClassification
import SBILeanProject.GR.KinematicsSynthesis
import SBILeanProject.GR.GeometricRepresentation
import SBILeanProject.GR.LocalConservation
import SBILeanProject.GR.StressEnergyBridge
import SBILeanProject.GR.LovelockClassification
import SBILeanProject.GR.EinsteinSynthesis
import SBILeanProject.GR.Conclusions

/-
Entry point for the General Relativity companion formalization.

The GR development is being added incrementally.  At this stage it imports:

  * ConstraintCapacity.lean
      packages the already formalized SBI persistence/frustration machinery
      into the reconfiguration-capacity language used in the GR manuscript;

  * ReachabilityBoundary.lean
      adds constraint-dependent local reachability, proves that stronger
      constraint families cannot enlarge the reachable domain, and formalizes
      the terminal limiting configuration for which no distinct continuation
      remains admissible;

  * MetricClosure.lean
      isolates the logical core of second-order metric closure.  It keeps the
      higher-order initial-data bridge explicit and proves that a closed
      metric-plus-first-rate state cannot support irreducibly higher-order
      dynamics requiring independent continuation data;

  * InertialPersistence.lean
      formalizes the pre-geometric content of Newton's first law: a physically
      meaningful change in propagation character requires relational support,
      so a persistent structure with no such support retains its propagation
      character;

  * CausalPropagation.lean
      imports the Time duration construction and states explicitly the GR
      bridge from relational propagation depth to duration-bearing reversible
      traversal, yielding the finite depth/duration bound;

  * InertialSymmetry.lean
      formalizes operational inertial equivalence and invariance of causal
      accessibility under operationally equivalent inertial redescription;

  * LorentzClassification.lean
      marks the final inertial classification as explicitly imported standard
      mathematics, with homogeneity, isotropy, relativity and finite invariant
      causal speed kept visible as hypotheses;

  * KinematicsSynthesis.lean
      collects Newton I, finite causal propagation, inertial/causal symmetry
      and the imported Lorentz result into one checked Section-2 spacetime
      kinematics result.  This result is an intermediate interface that feeds
      the later effective geometry rather than a terminal side branch;

  * GeometricRepresentation.lean
      keeps smooth manifold representability explicit, derives the Lorentzian
      causal character of that effective geometry from the checked kinematics
      through a separate local-geometry bridge, and derives coordinate
      invariance from relational closure;

  * LocalConservation.lean
      makes continuum local balance an explicit coarse-graining bridge and
      derives source-free local conservation for preserved quantities;

  * StressEnergyBridge.lean
      exposes the further representation step to a tensorial, symmetric and
      covariantly conserved effective source;

  * LovelockClassification.lean
      represents the four-dimensional Lovelock classification as explicitly
      imported standard mathematics;

  * EinsteinSynthesis.lean
      combines established effective Lorentzian geometry, second-order
      closure, the bridge into the Lovelock hypotheses, the external Lovelock
      classification, the conserved source, and an explicit geometric/source
      coupling to obtain the abstract Einstein-form field equation;

  * Conclusions.lean
      collects the remaining manuscript-facing destinations for the
      reachability/domain-of-validity branch and final effective GR dynamics.

The separate GR/DependencyReport.lean module may import this entry point to
construct machine-derived dependency maps without creating an import cycle.
-/
