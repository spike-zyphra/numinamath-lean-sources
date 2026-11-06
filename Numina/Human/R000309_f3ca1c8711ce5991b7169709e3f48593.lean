import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all positive integers  $x$ , for which the equation  $$ a+b+c=xabc $$
   has solution in positive integers. Solve the equation for these values of  $x$-/
theorem number_theory_8876 :
  {x : ℕ | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = x * a * b * c} = {1, 2, 3} := by
    ext x; simp; constructor <;> intro h
    · obtain ⟨a, ha, b, hb, c, hc, h⟩ := h
      -- we can get $x \leq 3$, otherwise $a + b + c = 3 * a * b * c$ has no positive integer
      -- solution for $a, b, c$.
      have : x ≤ 3 := by
        by_contra! tmp
        -- an auxiliary lemma : the value of `max (max a b) c` can only be `a, b, c`.
        have aux : (max (max a b) c = a ∨ max (max a b) c = b) ∨ max (max a b) c = c := by
          rcases le_or_gt (max a b) c with hl | hr
          · simp [hl]
          · have h1 : max (max a b) c = max a b := max_eq_left_of_lt hr
            rcases le_or_gt a b with hl | hl
            · have h2 : max a b = b := Nat.max_eq_right hl
              nth_rw 2 [h2] at h1; tauto
            · have h2 : max a b = a := Nat.max_eq_left (by linarith)
              nth_rw 2 [h2] at h1; tauto
        -- whatever `max (max a b) c` be, $3 < x$ is impossible.
        rcases aux with (h1 | h1) | h1
        · have h2 : a + b + c ≤ 3 * a := by
            have : b ≤ a := (Nat.le_max_right a b).trans (by
              have := Nat.le_max_left (max a b) c
              rw [h1] at this
              exact this)
            have : c ≤ a := by
              have := Nat.le_max_right (max a b) c
              rw [h1] at this
              exact this
            linarith
          have : 3 * a < x * a * b * c :=
            lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right tmp ha) (by
              rw [mul_assoc]; nth_rw 1 [←mul_one (x * a)]
              refine Nat.mul_le_mul_left (x * a) (Right.one_le_mul hb hc))
          linarith
        · have h2 : a + b + c ≤ 3 * b := by
            have : a ≤ b := (Nat.le_max_left a b).trans (by
              have := Nat.le_max_left (max a b) c
              rw [h1] at this
              exact this)
            have : c ≤ b := by
              have := Nat.le_max_right (max a b) c
              rw [h1] at this
              exact this
            linarith
          have h3 : 3 * b < x * a * b * c :=
            lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right tmp hb) (by
              rw [mul_assoc x a b, mul_comm a b, ←mul_assoc, mul_assoc]; nth_rw 1 [←mul_one (x * b)]
              refine Nat.mul_le_mul_left (x * b) (Right.one_le_mul ha hc))
          linarith
        · have h2 : a + b + c ≤ 3 * c := by
            have : a ≤ c := (Nat.le_max_left a b).trans (sup_eq_right.1 h1)
            have : b ≤ c := (Nat.le_max_right a b).trans (sup_eq_right.1 h1)
            linarith
          have h3 : 3 * c < x * a * b * c := by
            calc
              _ < x * c := Nat.mul_lt_mul_of_pos_right tmp hc
              _ ≤ x * a * b * c := Nat.mul_le_mul
                (by rw [mul_assoc]; refine Nat.le_mul_of_pos_right x (by simp; tauto)) (by simp)
          linarith
      -- $x \ne 0$.
      have xne0 : x ≠ 0 := by
        intro tmp; simp [tmp] at h; linarith
      -- Because $x \ne 0$ and $x \leq 3$, so $x = 1$ or $x = 2$ or $x = 3$.
      omega
    · -- Check that when $x = 1,2,3$, the equation $a + b + c = x * a * b * c$ has solution.
      rcases h with h1 | h2 | h3
      · exact ⟨1, by simp, 2, by simp, 3, by simp, by simp [h1]⟩
      · exact ⟨1, by simp, 1, by simp, 2, by simp, by simp [h2]⟩
      · exact ⟨1, by simp, 1, by simp, 1, by simp, by simp [h3]⟩
