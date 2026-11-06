import Mathlib

/-Let $N_0$ be a positive odd integer. Let $S = 4(N_0^2 + 6N_0 + 14)$.
Let $n$ be a positive natural number such that $n$ is odd.
If $S = n^2 + (n+2)^2 + (n+4)^2 + (n+6)^2$, show that $n=N_0$.-/
theorem number_theory_635817 {N₀ S n : ℕ} (hN₀ : Odd N₀) (hS₁ : S = 4 * (N₀^2 + 6 * N₀ + 14)) (hS₂ : S = n^2 + (n + 2)^2 + (n + 4)^2 + (n + 6)^2) : n = N₀ := by
  set f := fun n => n^2 + (n + 2)^2 + (n + 4)^2 + (n + 6)^2 with hf
  have hS₁' : S = f N₀ := by
    rw [hf, hS₁]
    ring_nf
  have hS₂' : S = f n := hS₂
  suffices StrictMono f by
    apply this.injective
    rw [←hS₁', ←hS₂']
  intro x y hxy
  simp only [hf]
  nlinarith
