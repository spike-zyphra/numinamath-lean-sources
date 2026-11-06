import Mathlib

/- Karl was attempting to calculate economic figures. He found the following equation to be true:\[fp-w=10000\]If $f=5$ and $w=5+125i$, what is $p$? -/
theorem algebra_10690 {f w p : ℂ} (hf : f = 5) (hw : w = 5 + 125 * .I) (h : f * p - w = 10000) :
    p = 2001 + 25 * .I := by
  subst_vars; simp [Complex.ext_iff] at h ⊢; constructor <;> linarith