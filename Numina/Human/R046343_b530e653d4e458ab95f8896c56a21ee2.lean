import Mathlib

/- 10.2. Given numbers $a, b, c$. It is known that for any $x$ the inequality


$$

a x^{2}+b x+c \geqslant b x^{2}+c x+a \geqslant c x^{2}+a x+b

$$


holds. Prove that $a=b=c$. -/
theorem inequalities_143807 (a b c : ℝ)
(h : ∀ x : ℝ, a * x^2 + b * x + c ≥ b * x^2 + c * x + a ∧ b * x^2 + c * x + a ≥ c * x^2 + a * x + b) :
    a = b ∧ b = c := by
    --Using `x = 0` we get two inequalities `c ≥ a` and `a ≥ b`.
    have h0 := h 0
    rcases h0 with ⟨h1, h2⟩
    have hcgea : c ≥ a := by linarith [h1]
    have hageb : a ≥ b := by linarith [h2]
    --Using `x = -1` we get the inequality `a ≥ c`.
    have hneg1 := h (-1)
    rcases hneg1 with ⟨h3, h4⟩
    have h3_1 : a - b + c ≥ b - c + a := by linarith [h3]
    have h4_1 : b - c + a ≥ c - a + b := by linarith [h4]
    have h4_1_1 : a ≥ c := by linarith [h4_1]
    --We get `a = c` using `c ≥ a` and `a ≥ c`.
    have haeqc : a = c := by
      apply le_antisymm
      exact hcgea
      exact h4_1_1
    --We are almost done. We get `b ≥ c` using `x = -2`.
    --Then we use the fact `a = c` to end the proof.
    have hneg2 := h (-2)
    rcases hneg2 with ⟨h5, h6⟩
    have h5_1 : 4 * a - 2 * b + c ≥ 4 * b - 2 * c + a := by linarith [h5]
    have h6_1 : 4 * b - 2 * c + a ≥ 4 * c - 2 * a + b := by linarith [h6]
    have h6_1_1 : 3 * b  - 6 * c + 3 * a ≥ 0 := by linarith [h6_1]
    rw [haeqc] at h6_1_1
    have h6_1_2 : 3 * b ≥ 3 * c := by linarith [h6_1_1]
    have hcleb : c ≤ b := by linarith [h6_1_2]
    have hblec : b ≤ c := by
      rw [haeqc] at hageb
      exact hageb
    have hbeqc : b = c := by exact le_antisymm hblec hcleb
    rw [←haeqc] at hcleb
    have haeqb : a = b := by exact le_antisymm hcleb hageb
    exact ⟨haeqb, hbeqc⟩