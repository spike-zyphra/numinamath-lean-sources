import Mathlib

open Real

namespace algebra_616488

/- $f (x) = 5 ^ x - 2 ^ x$ is strictly increasing when $x &gt; 0$-/
lemma mono : StrictMonoOn (fun x : ℝ => (5 : ℝ) ^ x - 2 ^ x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hxy' : 0 < y - x := sub_pos.mpr hxy
  simp only
  suffices : 2 ^ x * (2 ^ (y - x) - 1)  < (5 : ℝ) ^ x * (5 ^ (y - x) - 1)
  ring_nf at this
  have eq1 : (5 : ℝ) ^ x * 5 ^ (y - x) = 5 ^ y := by
    rw [← rpow_add (by norm_num)]
    simp
  have eq2 : (2 : ℝ) ^ x * 2 ^ (y - x) = 2 ^ y := by
    rw [← rpow_add (by norm_num)]
    simp
  rw [eq1, eq2] at this
  linarith only [this]
  have lt1 : 0 < (5 : ℝ) ^ (y - x) - 1 := by
    simp
    apply one_lt_rpow (by norm_num) hxy'
  have lt2 : 0 < (2 : ℝ) ^ (y - x) - 1 := by
    simp
    apply one_lt_rpow (by norm_num) hxy'
  gcongr
  simpa using hx
  all_goals norm_num

end algebra_616488

open algebra_616488

/- Solve the equation $5^x - 2^x = 3093$ for $x$.-/
theorem algebra_616488 {x : ℝ} : (5 : ℝ) ^ x - 2 ^ x = 3093 ↔ x = 5 := by
  constructor
  · -- First, we prove $x = 5$
    intro eq
    by_cases h : x ∈ Set.Ioi 0
    · let f : ℝ → ℝ := fun x => (5 : ℝ) ^ x - 2 ^ x
      -- Note that $f (x) = 5 ^ x - 2 ^ x$ is strictly increasing on $x &gt; 0$
      have finj := StrictMonoOn.injOn mono
      -- If $x &gt; 0$, then since$f$ is injective when $x > 0$ by monotonicity, it suffices to show $f (x) = f (5)$.
      apply finj h (by norm_num)
      -- It follows from direct computations.
      simp [f, eq]
      norm_num
    · simp at h
      rw [le_iff_lt_or_eq] at h
      -- If $x \le 0$, then $x > 0$ or $x = 0.$
      rcases h with (h | rfl)
      · -- If $x > 0$, then $5 ^ x - 2 ^ y > 0$. Contradiction.
        have contra : (5 : ℝ) ^ x - 2 ^ x < 0 := by
          simp
          refine rpow_lt_rpow_of_exponent_neg ?_ ?_ h
          <;> norm_num
        linarith
      -- If $x = 0$, contradiction.
      · norm_num at eq
  -- Second, easy to check $x = 5$ is a solution.
  · rintro ⟨rfl⟩
    norm_num
