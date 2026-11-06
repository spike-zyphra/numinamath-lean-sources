import Mathlib

theorem algebra_298594 {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Ioo (-1) 1, ∀ y ∈ Set.Ioo (-1) 1,
    f x + f y = f ((x + y) / (1 + x * y))) (a b : ℝ) (ha : a ∈ Set.Ioo (-1) 1) (hb : b ∈ Set.Ioo (-1) 1)
    (h : f ((a + b) / (1 + a * b)) = 1) (h' : f ((a - b) / (1 - a * b)) = 2) (h'' : |a| < 1) (h''' : |b| < 1) :
    f a = 3 / 2 ∧ f b = -1 / 2 := by
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  have eq1 : f a + f b = 1 := by
    have h1 := hf a (show a ∈ Set.Ioo (-1) 1 by constructor <;> linarith) b (show b ∈ Set.Ioo (-1) 1 by constructor <;> linarith)
    rw [h] at h1
    linarith
  have eq2 : f a + f (-b) = 2 := by
    have h2 := hf a (show a ∈ Set.Ioo (-1) 1 by constructor <;> linarith) (-b) (show -b ∈ Set.Ioo (-1) 1 by
      constructor
      · linarith [hb₁, hb₂]
      · linarith [hb₁, hb₂]
    )
    have h3 : (a + -b) / (1 + a * (-b)) = (a - b) / (1 - a * b) := by
      ring_nf
    rw [h3] at h2
    rw [h'] at h2
    linarith
  have eq3 : f 0 = 0 := by 
    have h3 := hf (0 : ℝ) (show (0 : ℝ) ∈ Set.Ioo (-1) 1 by 
      constructor <;> norm_num) (0 : ℝ) (show (0 : ℝ) ∈ Set.Ioo (-1) 1 by 
      constructor <;> norm_num
    )
    norm_num at h3
    linarith
  have eq4 : f (-b) + f b = f 0 := by 
    have h4 := hf (-b) (show -b ∈ Set.Ioo (-1) 1 by
      constructor
      · linarith [hb₁, hb₂]
      · linarith [hb₁, hb₂]
    ) b (show b ∈ Set.Ioo (-1) 1 by constructor <;> linarith)
    have h5 : (-b + b) / (1 + (-b) * b) = (0 : ℝ) := by 
      ring_nf 
    rw [h5] at h4 
    linarith 
  rw [eq3] at eq4 
  have eq5 : f (-b) = - f b := by 
    linarith [eq4]
  have hfa : f a = 3 / 2 := by 
    rw [eq5] at eq2 
    linarith [eq1, eq2]
  have hfb : f b = -1 / 2 := by 
    linarith [eq1, hfa]
  exact ⟨hfa, hfb⟩