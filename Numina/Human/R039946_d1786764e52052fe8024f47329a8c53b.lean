import Mathlib

open Cardinal

/- 39.22. Prove that the set of all points in a square has the power of the continuum.

## 39.6. Properties of Cardinality -/
theorem other_232190 (a b c d : ℝ) (hab : a < b) (hcd : c < d) : #(Set.Icc a b ×ˢ Set.Icc c d) = continuum
  := by
    -- cardinality distributes over set products
    rw [Cardinal.mk_setProd]

    -- non-empty intervals have cardinality of the continuum
    rw [Cardinal.mk_Icc_real hab, Cardinal.mk_Icc_real hcd]

    -- continuum * continuum = continuum
    exact continuum_mul_self