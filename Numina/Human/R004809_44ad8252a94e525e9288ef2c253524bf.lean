import Mathlib

open Real

/- Given an odd function \\(f(x)\\) defined on \\(\mathbb{R}\\) that satisfies \\(f(-x)=-f(x)\\), \\(f(x+1)=f(1-x)\\), and when \\(x \in [0,1]\\), \\(f(x)=\log_{2}(x+1)\\), then \\(f(31)=\\) ?

A: \\(0\\)
B: \\(1\\)
C: \\(-1\\)
D: \\(2\\) -/
theorem algebra_411508 {f : ℝ → ℝ} (hf₀ : ∀ x, f (-x) = -f x)
    (hf₁ : ∀ x, f (x + 1) = f (1 - x)) (hf₂ : ∀ x ∈ Set.Icc 0 1, f x = logb 2 (x + 1)) :
    f 31 = -1 := by
  have H x : f (x + 4) = f x := by
    calc
      _ = f ((x + 3) + 1) := by ring_nf
      _ = f (1 - (x + 3)) := by rw [hf₁]
      _ = f (-(x + 2)) := by ring_nf
      _ = -f (x + 2) := by rw [hf₀]
      _ = -f ((x + 1) + 1) := by ring_nf
      _ = -f (1 - (x + 1)) := by rw [hf₁]
      _ = -f (-x) := by ring_nf
      _ = f x := by simp [hf₀]
  have K x (n : ℕ) : f (x + 4 * n) = f x := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp [mul_add]
      rwa [← add_assoc, H]
  specialize K (-1) 8
  norm_num at K
  rw [K, hf₀, hf₂ 1 (by simp)]
  norm_num
