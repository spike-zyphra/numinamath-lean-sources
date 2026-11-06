import Mathlib

set_option maxHeartbeats 0

/-60. Let $a, b, c$ be non-negative numbers, no two of which are zero. Prove that
$$\frac{1}{b+c}+\frac{1}{c+a}+\frac{1}{a+b} \geqslant \frac{2 a}{3 a^{2}+b c}+\frac{2 b}{3 b^{2}+c a}+\frac{2 c}{3 c^{2}+a b}$$-/
theorem inequalities_599083 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h₁ : a + b ≠ 0) (h₂ : b + c ≠ 0) (h₃ : c + a ≠ 0) (h₄ : 3 * a ^ 2 + b * c ≠ 0)
    (h₅ : 3 * b ^ 2 + c * a ≠ 0) (h₆ : 3 * c ^ 2 + a * b ≠ 0) :
    1 / (b + c) + 1 / (c + a) + 1 / (a + b) ≥
    2 * a / (3 * a ^ 2 + b * c) + 2 * b / (3 * b ^ 2 + c * a) +
    2 * c / (3 * c ^ 2 + a * b) := by
  -- 60. (2007.02.09) Brief proof: By symmetry, without loss of generality, assume (a \geqslant b \geqslant c), then $$\begin{aligned} \sum \frac{1}{b+c}-\sum \frac{2 a}{3 a^{2}+b c}= & \sum \frac{(a-b)(a-c)+a(a-b)+a(a-c)}{(b+c)\left(3 a^{2}+b c\right)}= \ & {\left[\frac{(a-b)(a-c)}{(b+c)\left(3 a^{2}+b c\right)}-\frac{(a-b)(b-c)}{(c+a)\left(3 b^{2}+a c\right)}\right]+} \ & {\left[\frac{a(a-b)}{(b+c)\left(3 a^{2}+b c\right)}-\frac{b(a-b)}{(c+a)\left(3 b^{2}+a c\right)}\right]+} \ & {\left[\frac{b(b-c)}{(b+c)\left(3 a^{2}+b c\right)}-\frac{c(b-c)}{(a+b)\left(3 c^{2}+a b\right)}\right]+} \ & {\left[\frac{a(a-c)}{(b+c)\left(3 a^{2}+b c\right)}-\frac{c(a-c)}{(a+b)\left(3 c^{2}+a b\right)}\right]+} \ & \frac{(a-c)(b-c)}{(a+b)\left(3 c^{2}+a b\right)}= \ & \frac{c(a-b)^{2}\left(a^{2}+a b+b^{2}+3 a c+3 b c-c^{2}\right)}{(b+c)(c+a)\left(3 a^{2}+b c\right)\left(3 b^{2}+a c\right)}+ \ & \frac{c(a-b)^{3}+c^{2}\left(a^{2}-b^{2}\right)}{(b+c)(c+a)\left(3 a^{2}+b c\right)\left(3 b^{2}+a c\right)}+ \ & \frac{a(b-c)^{3}+a^{2}\left(b^{2}-c^{2}\right)}{(c+a)(a+b)\left(3 b^{2}+a c\right)\left(3 c^{2}+a b\right)}+ \ & \frac{b(a-c)^{3}+b^{2}\left(a^{2}-c^{2}\right)}{(b+c)(a+b)\left(3 a^{2}+b c\right)\left(3 c^{2}+a b\right)}+ \ \frac{(a-c)(b-c)}{(a+b)\left(3 c^{2}+a b\right)} \geqslant 0 & \end{aligned}$$
  wlog h : a ≥ b ∧ b ≥ c with H
  · simp at h
    by_cases hab : a ≥ b
    · obtain h := h hab
      by_cases hca : c ≥ a
      · obtain H := H c a b hc ha hb (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) ⟨hca, hab⟩
        apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
      · simp at hca
        obtain H := H a c b ha hc hb (by linarith) (by linarith) (by linarith) (by rw [mul_comm c]; exact h₄) (by rw [mul_comm b]; exact h₆) (by rw [mul_comm a]; exact h₅) ⟨le_of_lt hca, le_of_lt h⟩
        apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
    · simp at hab
      by_cases hcb : c ≥ b
      · obtain H := H c b a hc hb ha (by linarith) (by linarith) (by linarith) (by rw [mul_comm b]; exact h₆) (by rw [mul_comm a]; exact h₅) (by rw [mul_comm c]; exact h₄) ⟨hcb, le_of_lt hab⟩
        apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
      · simp at hcb
        by_cases hac : a ≥ c
        · obtain H := H b a c hb ha hc (by linarith) (by rw [add_comm]; exact h₃) (by linarith) (by rw [mul_comm a]; exact h₅) (by rw [mul_comm c]; exact h₄) (by rw [mul_comm b]; exact h₆) ⟨le_of_lt hab, hac⟩
          apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
        · simp at hac
          obtain H := H b c a hb hc ha (by linarith) (by linarith) (by linarith) (by positivity) (by positivity) (by positivity) ⟨le_of_lt hcb, le_of_lt hac⟩
          apply le_of_eq_of_le ?_ (le_of_le_of_eq H ?_) <;> ring
  · apply sub_nonneg.mp
    trans (1 / (b + c) - 2 * a / (3 * a ^ 2 + b * c)) +
        (1 / (c + a) - 2 * b / (3 * b ^ 2 + c * a)) +
        (1 / (a + b) - 2 * c / (3 * c ^ 2 + a * b))
    swap
    · apply le_of_eq
      ring
    trans ((a - b) * (a - c) + a * (a - b) + a * (a - c)) / ((b + c) * (3 * a ^ 2 + b * c)) +
        ((b - c) * (b - a) + b * (b - c) + b * (b - a)) / ((c + a) * (3 * b ^ 2 + c * a)) +
        ((c - a) * (c - b) + c * (c - a) + c * (c - b)) / ((a + b) * (3 * c ^ 2 + a * b))
    swap
    · gcongr
      all_goals
        field_simp
        apply le_of_eq
        congr 1
        ring
    trans ((a - b) * (a - c) / ((b + c) * (3 * a ^ 2 + b * c)) - (a - b) * (b - c) / ((c + a) * (3 * b ^ 2 + c * a))) + ((a * (a - b)) / ((b + c) * (3 * a ^ 2 + b * c)) - (b * (a - b)) / ((c + a) * (3 * b ^ 2 + c * a))) + ((b * (b - c)) / ((c + a) * (3 * b ^ 2 + c * a)) - (c * (b - c)) / ((a + b) * (3 * c ^ 2 + a * b))) + ((a * (a - c)) / ((b + c) * (3 * a ^ 2 + b * c)) - (c * (a - c)) / ((a + b) * (3 * c ^ 2 + a * b))) + ((a - c) * (b - c)) / ((a + b) * (3 * c ^ 2 + a * b))
    swap
    · apply le_of_eq
      rw [add_div, add_div, add_div, add_div, add_div, add_div]
      have : (a - c) * (b - c) / ((a + b) * (3 * c ^ 2 + a * b)) = (c - a) * (c - b) / ((a + b) * (3 * c ^ 2 + a * b)) := by
        field_simp
        ring
      rw [this]
      have : (a - b) * (b - c) / ((c + a) * (3 * b ^ 2 + c * a)) = - ((b - c) * (b - a) / ((c + a) * (3 * b ^ 2 + c * a))) := by
        field_simp
        ring
      rw [this, sub_neg_eq_add]
      have : b * (a - b) / ((c + a) * (3 * b ^ 2 + c * a)) = - (b * (b - a) / ((c + a) * (3 * b ^ 2 + c * a))) := by
        field_simp
        ring
      rw [this, sub_neg_eq_add]
      have : c * (b - c) / ((a + b) * (3 * c ^ 2 + a * b)) = - (c * (c - b) / ((a + b) * (3 * c ^ 2 + a * b))) := by
        field_simp
        ring
      rw [this, sub_neg_eq_add]
      have : c * (a - c) / ((a + b) * (3 * c ^ 2 + a * b)) = - (c * (c - a) / ((a + b) * (3 * c ^ 2 + a * b))) := by
        field_simp
        ring
      rw [this, sub_neg_eq_add]
      ring
    trans (c * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2 + 3 * a * c + 3 * b * c - c ^ 2)) /
    ((b + c) * (c + a) * (3 * a ^ 2 + b * c) * (3 * b ^ 2 + c * a)) +
    (a - b) * (c * (a - b) ^ 3 + c ^ 2 * (a ^ 2 - b ^ 2)) /
    ((b + c) * (c + a) * (3 * a ^ 2 + b * c) * (3 * b ^ 2 + c * a)) +
    (b - c) * (a * (b - c) ^ 3 + a ^ 2 * (b ^ 2 - c ^ 2)) /
    ((c + a) * (a + b) * (3 * b ^ 2 + c * a) * (3 * c ^ 2 + a * b)) +
    (a - c) * (b * (a - c) ^ 3 + b ^ 2 * (a ^ 2 - c ^ 2)) /
    ((b + c) * (a + b) * (3 * a ^ 2 + b * c) * (3 * c ^ 2 + a * b)) +
    ((a - c) * (b - c)) / ((a + b) * (3 * c ^ 2 + a * b))
    swap
    · apply le_of_eq
      congr
      · field_simp
        ring
      · field_simp
        ring
      · field_simp
        ring
      · field_simp
        ring
    · obtain ⟨h₁, h₂⟩ := h
      apply add_nonneg
      apply add_nonneg
      apply add_nonneg
      apply add_nonneg
      · apply div_nonneg
        · apply mul_nonneg
          apply mul_nonneg
          · positivity
          · positivity
          · trans (a - c) * (a + c) + a * b + b ^ 2 + 3 * a * c + 3 * b * c
            · apply add_nonneg
              · apply add_nonneg
                · apply add_nonneg
                  · apply add_nonneg
                    · apply mul_nonneg
                      · apply sub_nonneg_of_le (le_trans h₂ h₁)
                      · positivity
                    · positivity
                  · positivity
                · positivity
              · positivity
            · apply le_of_eq
              ring
        · positivity
      · apply div_nonneg
        · apply mul_nonneg
          · apply sub_nonneg_of_le h₁
          · apply add_nonneg
            · apply mul_nonneg
              · exact hc
              · apply pow_nonneg
                apply sub_nonneg_of_le h₁
            · apply mul_nonneg
              · positivity
              · trans (a - b) * (a + b)
                · apply mul_nonneg
                  · apply sub_nonneg_of_le h₁
                  · positivity
                · apply le_of_eq
                  ring
        · positivity
      · apply div_nonneg
        · apply mul_nonneg
          · apply sub_nonneg_of_le h₂
          · apply add_nonneg
            · apply mul_nonneg
              · exact ha
              · apply pow_nonneg
                apply sub_nonneg_of_le h₂
            · apply mul_nonneg
              · positivity
              · trans (b - c) * (b + c)
                · apply mul_nonneg
                  · apply sub_nonneg_of_le h₂
                  · positivity
                · apply le_of_eq
                  ring
        · positivity
      · apply div_nonneg
        · apply mul_nonneg
          · apply sub_nonneg_of_le (le_trans h₂ h₁)
          · apply add_nonneg
            · apply mul_nonneg
              · exact hb
              · apply pow_nonneg
                apply sub_nonneg_of_le (le_trans h₂ h₁)
            · apply mul_nonneg
              · positivity
              · trans (a - c) * (a + c)
                · apply mul_nonneg
                  · apply sub_nonneg_of_le (le_trans h₂ h₁)
                  · positivity
                · apply le_of_eq
                  ring
        · positivity
      · apply div_nonneg
        · apply mul_nonneg
          · apply sub_nonneg_of_le (le_trans h₂ h₁)
          · apply sub_nonneg_of_le h₂
        · positivity
