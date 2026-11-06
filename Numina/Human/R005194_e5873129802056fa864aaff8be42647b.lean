import Mathlib

-- Define a sequence z such that (z_n, z_(n+1)) satisfies the equation.
def z : ℕ → ℕ
| 0 => 1
| 1 => 2
| n + 2 => 4 * z (n + 1) - 1 - z n

-- Prove a lemma that z_(n + 1) ≥ 2z_n > 0 for all n.
lemma estimate (n : ℕ) : z (n + 1) ≥ 2 * z n ∧ z n > 0 := by
  -- Perform induction on n.
  induction' n with n hn
  . -- Base case n = 0.
    simp [z]
  . -- Inductive step.
    -- Expand the inductive definition of z.
    rw [z, ge_iff_le, <-@Nat.add_le_add_iff_right _ _ 1, <-Nat.sub_add_comm (by omega), Nat.sub_add_cancel (by omega)]
    refine ⟨?_, ?_⟩
    . -- Show that 2z_(n + 1) + 1 ≤ 4z_(n + 1) - z_n, which is equivalent to z_n + 1 ≤ 2z_(n + 1).
      omega
    . -- Verify that z_(n + 1) > 0.
      omega

/- Bewijs dat er oneindig veel paren positieve gehele getallen $(x, y)$ zijn met

$$
\frac{x+1}{y}+\frac{y+1}{x}=4 .
$$ -/
theorem number_theory_606173 :
    {(x, y) : ℕ × ℕ | 0 < x ∧ 0 < y ∧ ((x + 1) / y : ℚ) + ((y + 1) / x : ℚ) = 4}.Infinite := by
  -- Let S be the set of pairs (x, y) defined above.
  set S : Set (ℕ × ℕ) := {(x, y) | 0 < x ∧ 0 < y ∧ ((x + 1) / y : ℚ) + ((y + 1) / x : ℚ) = 4} with hS₀
  -- Show that the set of pairs (z_n, z_(n + 1)) belongs to S for all n.
  have h₀ (n : ℕ) : (z n, z (n + 1)) ∈ S := by
    -- Perform induction on n.
    induction' n with n hn
    . -- Base case n = 0.
      norm_num [z, hS₀]
    . -- Inductive step.
      -- We show that (z_(n + 1), z_(n + 2)) ∈ S if (z_n, z_(n + 1)) ∈ S.
      simp [S] at hn
      obtain ⟨hn₀, hn₁, hn⟩ := hn
      simp [S, hn₁]
      have h₀ := estimate n
      refine ⟨?_, ?_⟩
      . -- Verify that z_n < 4z_(n + 1) - 1.
        rw [z]
        omega
      . -- Verify that the equation holds.
        have h₁ : 0 < z (n + 1 + 1) := by
          rw [z]
          omega
        -- Clear denominators in both equations.
        field_simp at hn ⊢
        rw [z]
        norm_cast
        zify
        -- Use Vieta's formula to find another root according to hypothesis hn, which is equivalent to z_n ^ 2 - (4z_(n + 1) - 1)z_n + (z_(n + 1) ^ 2 + z_(n + 1)) = 0.
        replace hn : z n * z n - (4 * z (n + 1) - 1 : ℚ) * z n + (z (n + 1) ^ 2 + z (n + 1)) = 0 := by
          linarith
        obtain ⟨z', hz₀, hz₁, hz₂⟩ := vieta_formula_quadratic hn
        -- Now z' = 4z_(n + 1) - 1 - z_n = z_(n + 2).
        rw [show (4 * z (n + 1) - 1 - z n : ℕ) = ((4 * z (n + 1) : ℕ) - 1 - z n : ℤ) by rw [Nat.sub_sub, Int.natCast_sub (show 1 + z n ≤ 4 * z (n + 1) by omega), sub_sub]; norm_cast]
        qify
        rw [<-hz₁]
        linarith
  -- Assume on the contrary that S is finite, show that there would be a contradiction.
  by_contra hS₁
  simp at hS₁
  -- Let T = {(z n, z (n + 1)) | n ∈ ℕ}.
  let T : Set (ℕ × ℕ) := {(z n, z (n + 1)) | n : ℕ}
  -- Show that T ⊆ S and T is non-empty.
  have hS₂ : T ⊆ S := by
    -- For all n, (z n, z (n + 1)) is in S.
    intro n hn
    simp [T] at hn
    obtain ⟨n₀, hn⟩ := hn
    rw [<-hn]
    exact h₀ n₀
  have hS₃ : T.Nonempty := by
    -- Use the base case of the induction to show that (z 0, z 1) is in T.
    simp [T]
    use (z 0, z 1), 0
  have hS₄ := Set.Finite.exists_maximal_wrt (fun x => x.1 + x.2) T (Set.Finite.subset hS₁ hS₂) hS₃
  -- Let (z_n₀, z_(n₀ + 1)) be the maximal element in T.
  obtain ⟨⟨x, y⟩, hS₄, hS₅⟩ := hS₄
  simp [T] at hS₄ hS₅
  obtain ⟨n₀, ⟨rfl, rfl⟩⟩ := hS₄
  -- Use (z_(n₀ + 1), z_(n₀ + 2)) ∈ T to give a contradiction to the maximality of (z_n₀, z_(n₀ + 1)).
  specialize hS₅ (n₀ + 1)
  have hS₆ :  z n₀ + z (n₀ + 1) < z (n₀ + 1) + z (n₀ + 1 + 1) := by
    rw [z]
    have h₀ := estimate n₀
    omega
  simp [le_of_lt hS₆, hS₆.ne'.symm] at hS₅
