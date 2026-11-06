import Mathlib

open Polynomial
/- XXXVII OM - II - Problem 5
Prove that if a polynomial \$ f \$ not identically zero satisfies for every real \$ x \$ the equation \$ f(x)f(x + 3) = f(x^2 + x + 3) \$, then it has no real roots. -/
theorem algebra_115997 {f : Polynomial ℝ} (hf : f ≠ 0)
    (h : ∀ x, f.eval x * f.eval (x + 3) = f.eval (x ^ 2 + x + 3)) :
    ¬∃ x : ℝ, f.eval x = 0 := by 
  let g : ℝ → ℝ := fun x => x ^ 2 + x + 3
  --assume that there exists one such real root
  by_contra hexistsx
  obtain ⟨y, hy⟩ := hexistsx
  --then the set of root is infinite because iterating the function g is an injective operation, always producing a different root
  have rootset_infinite : (f.rootSet ℝ).Infinite := by 
    let G : ℕ → ℝ := fun n => g^[n] y
    --the iteration of g is injective because it is strictly monotone
    have G_inj : Function.Injective G := by 
      have G_smono: StrictMono G := by
        have Psucc : ∀ (n : ℕ), G n < G (n + 1) := by 
          intro n
          simp [G]
          rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
          simp [g]
          rw [add_assoc, add_comm _ 3, ← add_assoc]
          nth_rw 1 [← zero_add (g^[n] y)]
          exact add_lt_add_of_lt_of_le (add_pos_of_nonneg_of_pos (sq_nonneg (g^[n] y)) (by linarith)) (by rfl)
        exact strictMono_nat_of_lt_succ Psucc
      exact StrictMono.injective G_smono
    --if one has the polynoimal with the properties of the problem, then if y is a root then so is y^2+y+3.
    have is_root_of_root {f : Polynomial ℝ} {y : ℝ}
    (h : ∀ x, f.eval x * f.eval (x + 3) = f.eval (x ^ 2 + x + 3)) (hfy : f.eval y = 0) : f.eval (y ^ 2 + y + 3) = 0 := by 
      specialize h y
      rw[hfy] at h
      simpa using h.symm
    --all the iterations of g of the initial root are again roots by the above lemma
    have G_range_in_roots : Set.range G ⊆ f.rootSet ℝ := by 
      unfold Set.range rootSet
      simp[G]
      rw[Set.subset_def]
      intro x hx
      simp at hx ⊢
      obtain ⟨n, hn⟩ := hx
      constructor
      · exact hf
      · rw[← hn]
        have : ∀ m, eval (g^[m] y) f = 0 := by
          intro m
          induction m with
          | zero => 
          simp
          exact hy
          | succ d hd => 
          rw[Function.iterate_succ']
          simpa [g] using is_root_of_root h hd
        exact this n
    --the set of roots is infinite because it contains an infinite subset
    exact Set.Infinite.mono G_range_in_roots (Set.infinite_range_of_injective G_inj)
  --but the set of real roots of a polynomial is at most finite, hence this yields contradiction
  have rootset_finite := Polynomial.rootSet_finite f ℝ
  contradiction