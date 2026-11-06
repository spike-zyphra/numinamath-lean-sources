import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all fractions which can be written simultaneously in the forms
  $\frac{7k- 5}{5k - 3}$  and  $\frac{6l - 1}{4l - 3}$ , for some integers  $k, l$ .-/
theorem number_theory_8625 :
  {(k, l) : ℤ × ℤ | divInt (7 * k - 5 ) (5 * k - 3) = divInt (6 * l - 1) (4 * l - 3)} =
  {(0,6), (1,-1), (6,-6), (13,-7), (-2,-22), (-3,-15), (-8,-10), (-15,-9)} := by
    ext x
    simp
    constructor <;> intro h
    · -- We start with the given equation:
      -- \[
      -- \frac{7k - 5}{5k - 3} = \frac{6l - 1}{4l - 3}
      -- \]
      -- Cross-multiplying to eliminate the fractions, we get:
      -- \[
      -- (7k - 5)(4l - 3) = (5k - 3)(6l - 1)
      -- \]
      rw [Rat.divInt_eq_iff (by omega) (by omega)] at h
      -- Rearranging the equation, we have:
      -- \[
      -- (k + 1)(l + 8) = 14
      -- \]
      have c1 : (x.1 +1) * (x.2 + 8) = 14 := by linarith
      -- Auxiliary lemma : if the product of two integers is 14, all the possible values of
      -- them are followings.
      have aux : ∀ a b : ℤ, a * b = 14 → a = 1 ∧ b = 14 ∨ a = -1 ∧ b = -14 ∨
        a = 2 ∧ b = 7 ∨ a = -2 ∧ b = -7 ∨ a = 7 ∧ b = 2 ∨ a = -7 ∧ b = -2 ∨
        a = 14 ∧ b = 1 ∨ a = -14 ∧ b = -1 := by
          intro a b hab
          have c1 : a ∣ 14 := Dvd.intro b hab
          have : -14 ≤ a := by
            rw [←Int.neg_dvd] at c1
            have := Int.le_of_dvd (by decide) c1
            linarith
          have : a ≤ 14 := Int.le_of_dvd (by decide) c1
          have ane0 : a ≠ 0 := fun h => (by simp [h] at hab)
          have c2 : b = 14 / a := by refine Int.eq_ediv_of_mul_eq_right ane0 hab
          interval_cases a <;> norm_num at c2 <;> simp [c2] at hab ⊢
      -- use the auxiliay lemma to get possible of $k, l$.
      have c2 := aux (x.1 + 1) (x.2 + 8) c1
      simp [Prod.eq_iff_fst_eq_snd_eq]
      rcases c2 with h | h | h | h | h | h | h | h <;>
        ( have h2 := eq_sub_of_add_eq h.1
          have h3 := eq_sub_of_add_eq h.2
          simp at h2 h3
          simp [h2, h3])
    · -- Substituting each pair \((k, l)\) back into the original fractions to verify,
      -- we find that all pairs satisfy the equation.
      rcases h with h | h | h | h | h | h | h | h <;> simp [h] <;> decide
