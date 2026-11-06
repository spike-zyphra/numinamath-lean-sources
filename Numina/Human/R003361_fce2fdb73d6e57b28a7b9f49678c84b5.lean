import Mathlib
open Finset


/- $1 \cdot 7$ Let $a_{n}$ be the unit digit of $1^{2}+2^{2}+\cdots+n^{2}$, $n=1,2,3, \cdots$ Prove that: $0 . a_{1} a_{2} \cdots a_{n} \cdots$ is a rational number. -/
theorem number_theory_172697 (a : ℕ → ℕ)
  (ha : ∀ n, a n = (∑ k in range n, k^2) % 10) :
  ∃ m, ∀ n, a (n + m) = a n := by
  -- We claim that a (n + 100) = a n
  use 100
  intro n
  rw [ha n, ha (n + 100), Finset.sum_range_add]
  -- sum to n can be cancelled from both sides
  suffices (∑ i ∈ range 100, (n + i)^2) % 10 = 0 by rw [Nat.add_mod, this]; simp

  -- k^2, (k + 10)^2, ..., (k + 90)^2 are all the same mod 10
  have mod_eq : ∀ k : ℕ, ∀ i : Fin 10, (k + 10 * ↑i)^2 % 10 = k^2 % 10 := by intro k i; calc
    (k + 10 * i)^2 % 10 = (2 * k * i * 10 + k^2 + i^2 * 10 * 10) % 10 := by congr; ring
    _ = ((2 * k * i * 10) % 10 + (k^2 % 10) + (i^2 * 10 * 10) % 10) % 10 := by rw [Nat.add_mod, Nat.add_mod _ (k^2) 10, Nat.mod_add_mod]
    _ = k^2 % 10 := by simp

  -- so k^2 + (k + 10)^2 + ... + (k + 90)^2 = 10 * k^2 (mod 10) = 0
  have mod0 : ∀ k, (∑ i in range 10, (k + 10 * i)^2) % 10 = 0
  · intro k
    rw [Finset.sum_nat_mod, Finset.sum_range]
    conv_lhs => enter [1, 2, i]; rw [mod_eq k i]
    simp

  -- now rearrange the main sum
  have rearr : ∀ (f : ℕ → ℕ), ∑ k in range 100, f k = ∑ i in range 10, ∑ j in range 10, f (i + 10 * j)
  · intro f
    rw [
      ←sum_product' (range 10) (range 10) (fun i j ↦ f (i + 10 * j)),
      sum_bij' (fun k _ => (k % 10, k / 10)) (fun p _ => p.1 + 10 * p.2)
    ]
    · intro i hi
      simp only [mem_product, mem_range] at hi ⊢
      exact ⟨Nat.mod_lt _ (by norm_num), Nat.div_lt_of_lt_mul hi⟩
    · intro ⟨i, j⟩ hp
      simp only [mem_product, mem_range] at hp ⊢
      linarith
    · intro i hi
      simp only [mem_range] at hi ⊢
      exact Nat.mod_add_div i 10
    · intro ⟨i, j⟩ hp
      simp at hp ⊢
      rw [mul_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.add_left_eq_self]
      exact ⟨hp.left, Nat.div_eq_of_lt hp.left⟩
    · intro i hi
      congr
      exact (Nat.mod_add_div i 10).symm

  -- conclude using the above results
  rw [rearr (fun i ↦ (n + i)^2), Finset.sum_nat_mod]
  conv_lhs => enter [1, 2, i, 1, 2, j]; rw [←add_assoc]
  conv_lhs => enter [1, 2, i]; rw [mod0 (n + i)]
  simp only [sum_const_zero, Nat.zero_mod]