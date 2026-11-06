import Mathlib

namespace algebra_116313

lemma eq_pair_cases {a b c d : ℝ} (hab : a ≠ b) (hacd : a = c ∨ a = d) (hbc : b = c ∨ b = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp_all only [ne_eq]
  cases hacd with
  | inl h =>
    cases hbc with
    | inl h_1 =>
      subst h_1 h
      simp_all only [not_true_eq_false]
    | inr h_2 =>
      subst h_2 h
      simp_all only [and_self, false_and, or_false]
  | inr h_1 =>
    cases hbc with
    | inl h =>
      subst h_1 h
      simp_all only [false_and, and_self, or_true]
    | inr h_2 =>
      subst h_1 h_2
      simp_all only [not_true_eq_false]

end algebra_116313

open algebra_116313

/-Example 3 Let $M=\{a, a+d, a+2 d\}, P=\left\{a, a q, a q^{2}\right\}$, where $a$ is not equal to $0, M=$ $P$, find the value of $q$.
Translate the above text into English, please retain the original text's line breaks and format, and output the translation result directly.-/
theorem algebra_116313 {a d q : ℝ} (ha : a ≠ 0) {M P : Set ℝ} (hMP : M = P)
    (hM : M = { a, a + d, a + 2 * d }) (hP : P = ({ a, a * q, (a * q ^ 2) } : Set ℝ))
    (hM1 : [a, a + d, a + 2 * d].Nodup) (hP1 : [a, a * q, (a * q ^ 2)].Nodup) :
    q = - 1 / 2 := by
  have h1 : a + d ∈ P := by
    rw [← hMP, hM]
    simp
  have h2 : a + 2 * d ∈ P := by
    rw [← hMP, hM]
    simp
  have dneq : d ≠ 0 := by
    intro hd
    rw [hd] at hM1
    simp at hM1
  subst hP
  simp [dneq] at h1 h2
  have hneq : a + d ≠ a + 2 * d := by
    intro h
    simp [h] at hM1
  -- Since $M=P$, $a + d = aq, a + 2 d = aq² $ or $a + d = aq², a +2d= aq$
  have h3 := eq_pair_cases hneq h1 h2
  have hq : q - 1 ≠ 0 := by
    intro hq
    rw [sub_eq_zero] at hq
    simp [hq] at hP1
  rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩
  -- In the first case,
  -- $a + d = aq, a + 2 d = aq² \Rightarrow d = aq²-aq \Rightarrow a + aq²-aq = aq$
  · rw [two_mul, ← add_assoc] at h3b
    rw [h3a] at h3b
    have hd : d = a * q ^ 2 - a * q := by linarith [h3b]
    rw [hd] at h3a
    -- Since $a \neq 0$, $1+q²-q=q$
    have : 1 + (q ^ 2 - q) = q := by
      rw [← mul_right_inj' ha]
      rw [← h3a]
      ring
    rw [← sub_eq_zero] at this
    have : (q - 1) ^ 2 = 0 := by
      rw [← this]
      ring
    -- Then $q=1$.Contradiction
    simp at this
    exact absurd this hq
-- In the second case, similiarly, we can get
-- $1+q-q=q²$. Then $q=-\frac{1}{2}$.
  · rw [two_mul, ← add_assoc] at h3b
    rw [h3a] at h3b
    have hd : d = a * q - a * q ^ 2 := by linarith [h3b]
    rw [hd] at h3a
    have : 1 + q - q ^ 2 = q ^ 2 := by
      rw [← mul_right_inj' ha]
      rw [← h3a]
      ring
    rw [eq_comm, ← sub_eq_zero] at this
    have : (2 * q + 1) * (q - 1) = 0 := by
      rw [← this]
      ring
    simp [mul_eq_zero, hq] at this
    field_simp
    rw [← sub_eq_zero, ← this]
    ring
