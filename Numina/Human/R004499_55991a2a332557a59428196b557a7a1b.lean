import Mathlib

open Real Set
open scoped BigOperators
/-(15) 1 Represent the set using the roster method: $A=\left\{x \left\lvert\, x=\frac{a}{|a|}+\frac{|b|}{b}+\frac{|c|}{c}+\frac{a b c}{|a b c|}\right., a, b\right.$, $c \in \mathbf{R}, a b c \neq 0\}$ is . $\qquad$-/
theorem algebra_275657 :
  {x : ℝ | ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    x = a / abs a + abs b / b + abs c / c + a * b * c / abs (a * b * c)} = {-4, 0, 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the set on the left
      rintro ⟨a, b, c, ha, hb, hc, hx⟩
      have h1 : a / abs a = 1 ∨ a / abs a = -1 := by
        have h1 : abs a ≠ 0 := by
          intro h
          have : abs a = 0 := by linarith
          have : a = 0 := abs_eq_zero.mp this
          contradiction
        have h2 : a / abs a = 1 ∨ a / abs a = -1 := by
          by_cases h : a > 0
          · -- If a > 0, then a / |a| = 1
            have h3 : abs a = a := abs_of_pos h
            have h4 : a / abs a = 1 := by
              rw [h3]
              field_simp [h1]
            exact Or.inl h4
          · -- If not a > 0, then a ≤ 0
            by_cases h' : a < 0
            · -- If a < 0, then a / |a| = -1
              have h3 : abs a = -a := abs_of_neg h'
              have h4 : a / abs a = -1 := by
                rw [h3]
                field_simp [h1]
              exact Or.inr h4
            · -- If a = 0, contradiction
              have h3 : a = 0 := by linarith
              contradiction
        exact h2
      have h2 : abs b / b = 1 ∨ abs b / b = -1 := by
        have h1 : abs b ≠ 0 := by
          intro h
          have : abs b = 0 := by linarith
          have : b = 0 := abs_eq_zero.mp this
          contradiction
        have h2 : abs b / b = 1 ∨ abs b / b = -1 := by
          by_cases h : b > 0
          · -- If b > 0, then |b| / b = 1
            have h3 : abs b = b := abs_of_pos h
            have h4 : abs b / b = 1 := by
              rw [h3]
              field_simp [h1]
            exact Or.inl h4
          · -- If not b > 0, then b ≤ 0
            by_cases h' : b < 0
            · -- If b < 0, then |b| / b = -1
              have h3 : abs b = -b := abs_of_neg h'
              have h4 : abs b / b = -1 := by
                rw [h3]
                field_simp [h1]
              exact Or.inr h4
            · -- If b = 0, contradiction
              have h3 : b = 0 := by linarith
              contradiction
        exact h2
      have h3 : abs c / c = 1 ∨ abs c / c = -1 := by
        have h1 : abs c ≠ 0 := by
          intro h
          have : abs c = 0 := by linarith
          have : c = 0 := abs_eq_zero.mp this
          contradiction
        have h2 : abs c / c = 1 ∨ abs c / c = -1 := by
          by_cases h : c > 0
          · -- If c > 0, then |c| / c = 1
            have h3 : abs c = c := abs_of_pos h
            have h4 : abs c / c = 1 := by
              rw [h3]
              field_simp [h1]
            exact Or.inl h4
          · -- If not c > 0, then c ≤ 0
            by_cases h' : c < 0
            · -- If c < 0, then |c| / c = -1
              have h3 : abs c = -c := abs_of_neg h'
              have h4 : abs c / c = -1 := by
                rw [h3]
                field_simp [h1]
              exact Or.inr h4
            · -- If c = 0, contradiction
              have h3 : c = 0 := by linarith
              contradiction
        exact h2
      have h4 : a * b * c / abs (a * b * c) = (a / abs a) * (abs b / b) * (abs c / c) := by
        have h1 : abs (a * b * c) = abs a * abs b * abs c := by
          rw [abs_mul, abs_mul]
        have h2 : abs a ≠ 0 := by
          intro h
          have : abs a = 0 := by linarith
          have : a = 0 := abs_eq_zero.mp this
          contradiction
        have h3 : abs b ≠ 0 := by
          intro h
          have : abs b = 0 := by linarith
          have : b = 0 := abs_eq_zero.mp this
          contradiction
        have h4 : abs c ≠ 0 := by
          intro h
          have : abs c = 0 := by linarith
          have : c = 0 := abs_eq_zero.mp this
          contradiction
        field_simp [h1, h2, h3, h4]
        ring_nf
        field_simp [h2, h3, h4]
        ring
      rw [h4] at hx
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rw [hx] <;> simp [h1, h2, h3] <;> norm_num
    · -- Show that if x is in {-4, 0, 4}, then it is in the set on the left
      rintro (h | h | h)
      · -- x = -4
        use -1, -1, -1
        norm_num [h]
      · -- x = 0
        use 1, -1, -1
        norm_num [h]
      · -- x = 4
        use 1, 1, 1
        norm_num [h]
