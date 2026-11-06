import Mathlib

theorem algebra_181025 {f : ℝ → ℝ → ℝ} (h1 : ∀ a, f 0 a = a) (h2 : ∀ a b c, f a (f b c) = f c (f b a)) :
    ∀ a b c, f a (f b c) = f (f a b) c := by
  have h3 : ∀ a c, f a c = f c a := by
    intro a c
    have eq1 : f a (f 0 c) = f c (f 0 a) := h2 a 0 c
    have eq2 : f a (f 0 c) = f a c := by
      have h4 : f 0 c = c := by 
        apply h1
      simp [h4] 
    have eq3 : f c (f 0 a) = f c a := by
      have h4 : f 0 a = a := by 
        apply h1
      simp [h4] 
    rw [eq2] at eq1
    rw [eq3] at eq1
    linarith 
  intro a b c 
  have eq4 : f a (f b c) = f c (f b a) := h2 a b c
  have eq5 : f b a = f a b := by
    apply h3
  have eq6 : f c (f b a) = f c (f a b) := by 
    rw [eq5]
  have eq7 : f c (f a b) = f (f a b) c := by 
    have h4 : f c (f a b) = f (f a b) c := by 
      apply h3 
    linarith [h4]
  rw [eq4, eq6, eq7]