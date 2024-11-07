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

- Canonical stlc: big-step, call-by-value: [pub/stlc.v](stlc.v)

- Stlc in small-step, call-by-name: [pub/stlc_smallstep.v](stlc_smallstep.v)

- Stlc with step-indexed LR: [pub/stlc_indexed.v](stlc_indexed.v)

- Stlc binary LR: [pub/stlc_equiv.v](stlc_equiv.v)


STLC with boolean refs:

- Stlc with boolean refs: [pub/stlc_refb.v](stlc_refb.v)

- Stlc with boolean refs, binary LR: [pub/stlc_refb_equiv.v](stlc_refb_equiv.v)

- Stlc with boolean refs, step-indexed LR: [pub/stlc_refb_indexed.v](stlc_refb_indexed.v)


STLC with higher-order refs:

- Stlc with full higher-order refs, step-indexed LR: [pub/stlc_ref_indexed.v](stlc_ref_indexed.v)


STLC with effects:

- Stlc with boolean refs, binary LR and boolean yes/no effects: [pub/stlc_refb_effb_equiv.v](stlc_refb_effb_equiv.v)

  	Includes a proof of store-invariance for pure expressions.
  	Val_type has a 'useable' flag encoding if a value may be
  	used in an effectful way in the future.


STLC with parametric types (System F):

- System F [pub/stlc_tabs.v](stlc_tabs.v)


## Contributors

Part of the code is derived from the mechanizations of 
[https://github.com/tiarkrompf/minidot](Dependent Object Types (DOT)) 
and [https://github.com/tiarkrompf/reachability](Reachability Types).
Contributors include Nada Amin, Yuyan Bao, Oliver Bračevac, David Deng,
Siyuan He, Songlin Jia, Yueyang Tang, Fei Wang, Guannan Wei.
