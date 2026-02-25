# Types and Proofs

Mechanized baselines for various type systems, currently focused on
logical relations. 

Variants include small-step and big-step semantics, call-by-name
and call-by-value semantics, unary and binary logical relations, type-indexed
and step-indexed logical relations, pure and impure languages.

The focus is on end-to-end implementations using elementary 
techniques. The proofs use no fancy tactics, no fancy binding libraries, 
no fancy non-standard logics (Turkish Pistol Shooter Meme here).


## Contents

STLC variations:

- Canonical stlc: big-step, call-by-value: [stlc.v](pub/stlc.v)

- Stlc in small-step, call-by-name: [stlc_smallstep.v](pub/stlc_smallstep.v)

- Stlc normalization by evaluation: [stlc_nbe.v](pub/stlc_nbe.v)

- Stlc with step-indexed LR: [stlc_indexed.v](pub/stlc_indexed.v)

- Stlc with step-indexed LR and recursive functions: [stlc_rec_indexed.v](pub/stlc_rec_indexed.v)

- Stlc binary LR: [stlc_equiv.v](pub/stlc_equiv.v)

- Stlc binary LR with proof of beta equivalence: [stlc_equiv_beta.v](pub/stlc_equiv_beta.v)

- Stlc with step-indexed binary LR: [stlc_indexed_equiv.v](pub/stlc_indexed_equiv.v)

- Stlc with subtyping: [stlc_stp.v](pub/stlc_stp.v)


STLC with boolean refs:

- Stlc with boolean refs: [stlc_refb.v](pub/stlc_refb.v)

- Stlc with boolean refs, binary LR: [stlc_refb_equiv.v](pub/stlc_refb_equiv.v)

- Stlc with boolean refs, step-indexed LR: [stlc_refb_indexed.v](pub/stlc_refb_indexed.v)


STLC with higher-order refs:

- Stlc with full higher-order refs, step-indexed LR: [stlc_ref_indexed.v](pub/stlc_ref_indexed.v)


STLC with effects:

- Stlc with boolean refs, binary LR and boolean yes/no effects: [stlc_refb_effb_equiv.v](pub/stlc_refb_effb_equiv.v)

  	Includes a proof of store-invariance for pure expressions.
  	Val_type has a 'useable' flag encoding if a value may be
  	used in an effectful way in the future.

- Stlc with boolean refs, binary LR and boolean yes/no effects: [stlc_refb_effb_equiv_beta.v](pub/stlc_refb_effb_equiv_beta.v)

	Includes a proof of beta reduction for pure argument expressions.
	This version does not use a 'useable' flag on values, instead it
	splits exp_type into pure and impure versions.

- Stlc with non-termination tracked as effect: [stlc_rec_indexed_eff.v](pub/stlc_rec_indexed_eff.v)

	Combined termination and soundness proof, combining
	type-indexed and step-indexed LR. 


STLC with type equivalence and normalization:

- Stlc with type normalization [stlc_type_equiv.v](pub/stlc_type_equiv.v)


STLC with parametric types (System F):

- System F [stlc_tabs.v](pub/stlc_tabs.v)

- Variations: [stlc_tabs2.v](pub/stlc_tabs2.v),  [stlc_tabs3.v](pub/stlc_tabs3.v)


## Contributors

Part of the code is derived from the mechanizations of 
[Dependent Object Types (DOT)](https://github.com/tiarkrompf/minidot) 
and [Reachability Types](https://github.com/tiarkrompf/reachability).
Contributors include Nada Amin, Yuyan Bao, Oliver Bračevac, David Deng,
Siyuan He, Songlin Jia, Yueyang Tang, Fei Wang, Guannan Wei.
