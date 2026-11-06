import Mathlib

def f (n : ℕ) : ℕ := if n ≤ 25 then 2 * n else n - 12

theorem number_theory_1394 (a b c d : ℕ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : f^[2] a = 36) (h2 : f^[2] b = 36)
    (h3 : f^[2] c = 36) (h4 : f^[2] d = 36) :
    a + b + c + d = 123 := by 
  have h5 : a = 9 ∨ a = 30 ∨ a = 24 ∨ a = 60 := by
    have h11 : f^[2] a = 36 := h1
    have h111 : f (f a) = 36 := by
      simpa using h11
    have h112 : a = 9 ∨ a = 30 ∨ a = 24 ∨ a = 60 := by
      have h113 : a ≤ 60 := by
        by_contra h
        push_neg at h
        have h31 : a > 60 := h
        have h32 : f a = a - 12 := by
          simp [f]
          all_goals omega
        have h33 : f (f a) = (a - 12) - 12 := by
          rw [h32]
          simp [f]
          all_goals omega
        omega
      interval_cases a <;> norm_num [f, Function.iterate_succ_apply'] at h111 ⊢
      <;> tauto
    assumption
  have h6 : b = 9 ∨ b = 30 ∨ b = 24 ∨ b = 60 := by
    have h22 : f^[2] b = 36 := h2
    have h221 : f (f b) = 36 := by
      simpa using h22
    have h222 : b = 9 ∨ b = 30 ∨ b = 24 ∨ b = 60 := by
      have h223 : b ≤ 60 := by
        by_contra h
        push_neg at h
        have h31 : b > 60 := h
        have h32 : f b = b - 12 := by
          simp [f]
          all_goals omega
        have h33 : f (f b) = (b - 12) - 12 := by
          rw [h32]
          simp [f]
          all_goals omega
        omega
      interval_cases b <;> norm_num [f, Function.iterate_succ_apply'] at h221 ⊢
      <;> tauto
    assumption
  have h7 : c = 9 ∨ c = 30 ∨ c = 24 ∨ c = 60 := by
    have h33 : f^[2] c = 36 := h3
    have h331 : f (f c) = 36 := by
      simpa using h33
    have h332 : c = 9 ∨ c = 30 ∨ c = 24 ∨ c = 60 := by
      have h333 : c ≤ 60 := by
        by_contra h
        push_neg at h
        have h31 : c > 60 := h
        have h32 : f c = c - 12 := by
          simp [f]
          all_goals omega
        have h33 : f (f c) = (c - 12) - 12 := by
          rw [h32]
          simp [f]
          all_goals omega
        omega
      interval_cases c <;> norm_num [f, Function.iterate_succ_apply'] at h331 ⊢
      <;> tauto
    assumption
  have h8 : d = 9 ∨ d = 30 ∨ d = 24 ∨ d = 60 := by
    have h44 : f^[2] d = 36 := h4
    have h441 : f (f d) = 36 := by
      simpa using h44
    have h442 : d = 9 ∨ d = 30 ∨ d = 24 ∨ d = 60 := by
      have h443 : d ≤ 60 := by
        by_contra h
        push_neg at h
        have h31 : d > 60 := h
        have h32 : f d = d - 12 := by
          simp [f]
          all_goals omega
        have h33 : f (f d) = (d - 12) - 12 := by
          rw [h32]
          simp [f]
          all_goals omega
        omega
      interval_cases d <;> norm_num [f, Function.iterate_succ_apply'] at h441 ⊢
      <;> tauto
    assumption
  -- We need to show that a, b, c, d are the four distinct values
  -- This is true since they are distinct and can only be one of the four values
  have h9 : a + b + c + d = 123 := by
    have ha1 : a = 9 ∨ a = 30 ∨ a = 24 ∨ a = 60 := h5
    have hb1 : b = 9 ∨ b = 30 ∨ b = 24 ∨ b = 60 := h6
    have hc1 : c = 9 ∨ c = 30 ∨ c = 24 ∨ c = 60 := h7
    have hd1 : d = 9 ∨ d = 30 ∨ d = 24 ∨ d = 60 := h8
    omega
  exact h9