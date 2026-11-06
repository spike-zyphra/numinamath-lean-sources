import Mathlib

/-For how many integers $x$ do we have $\frac14 < \frac{x}{5} < \frac23$?-/
theorem algebra_20984 :
  Set.ncard {x : ℤ | (1 : ℝ) / 4 < x / 5 ∧ x / 5 < (2 : ℝ) / 3} = 2 := by
    -- we only need to prove that the required set is {2, 3}.
    suffices {x : ℤ | (1 : ℝ) / 4 < x / 5 ∧ x / 5 < (2 : ℝ) / 3} = {2, 3} by
      rw [this, Set.ncard_pair (by omega)]
    ext x
    simp
    -- Since we are looking for integer solutions, we should isolate $x$ by multiplying by 5.  This gives \[1\frac14<x<3\frac13.\]The only integers between $1\frac14$ and $3\frac13$ are 2 and 3.  Therefore there are $\boxed{2}$ integers that solve this pair of inequalities.
    constructor
    · intro ⟨h1, h2⟩ 
      norm_num [div_lt_iff₀] at h1 h2
      rw [lt_div_iff₀ (by simp)] at h2 
      norm_cast at h2
      have _ : x < 4 := by linarith 
      replace h1 : (5 : ℝ) < x * 4 := by linarith
      norm_cast at h1
      have _ : 1 < x := by linarith
      omega
    · intro hx
      rcases hx with hx | hx
      <;> norm_num [hx]
