import Mathlib
open Set

/- Given that $f(x) = x^k$ where $k > 0$, what is the range of $f(x)$ on the interval $[1, \infty)$? -/
theorem algebra_10314 (k : ℝ) (hk : k > 0) (f : ℝ → ℝ) (hf : f = fun x => x ^ k) : image f (Ici 1) = Ici 1 := by
  -- We have two goals to prove
  -- 1. f(x) ≥ 1 for all x ≥ 1
  -- 2. For any y ≥ 1, there exists an x ≥ 1 such that f(x) = y
  simp [image, Ici]
  ext y
  constructor
  . -- First goal
    rintro ⟨x, h, rfl⟩
    simp [hf]
    -- Use the library lemma Real.one_le_rpow to prove x^k ≥ 1
    exact Real.one_le_rpow h (le_of_lt hk)
  . simp_intro h
    -- f(y^(1/k)) = y
    use y ^ (1 / k)
    constructor
    . -- y^(1/k) ≥ 1 by the same library lemma
      exact Real.one_le_rpow h (one_div_nonneg.2 (le_of_lt hk))
    . -- (y^(1/k))^k = y
      -- Because y > 0, k ≠ 0
      simp [hf,
          ← Real.rpow_mul (show y ≥ 0 by linarith only [h]),
          show k ≠ 0 by linarith only [hk]]
