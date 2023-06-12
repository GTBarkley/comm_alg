import Mathlib


--class GradedRing 

variable [GradedRing S]

namespace DirectSum

namespace ideal

def S_+ := ⊕ (i ≥ 0) S_i

lemma  A set of homogeneous elements fi∈S+ generates S as an algebra over S0 ↔ they generate S+ as an ideal of S.