import Mathlib

def lucas (n : ℕ) : ℕ := match n with
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

theorem algebra_182076 {φ ψ : ℝ} (hφ : φ = (1 + √5) / 2) (hψ : ψ = (1 - √5) / 2)
    (n : ℕ) :
    lucas n = φ ^ n + ψ ^ n := by
  have h1 : ∀ (n : ℕ), ((lucas n : ℝ)) = φ ^ n + ψ ^ n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      -- Base Case: L_0 = 2
      -- We need to show (lucas 0 : ℝ) = φ ^ 0 + ψ ^ 0, which is 2 = 1 + 1
      simp [lucas]
      <;> norm_num [hφ, hψ]
      <;> ring_nf
      <;> norm_num
    | succ n =>
      cases n with
      | zero =>
        -- Base Case: L_1 = 1
        -- We need to show (lucas 1 : ℝ) = φ ^ 1 + ψ ^ 1, which is 1 = φ + ψ
        simp [lucas, hφ, hψ]
        <;> ring_nf
        <;> norm_num
        <;> ring_nf
        <;> norm_num
      | succ n =>
        -- Inductive Step: Assume it holds for n and n+1, prove for n+2
        have h2 := ih (n) (by linarith)
        have h3 := ih (n + 1) (by linarith)
        simp [lucas, h2, h3]
        <;> norm_num [hφ, hψ]
        <;> ring_nf
        <;> norm_num
        <;> ring_nf
        <;> norm_num
        all_goals norm_num [hφ, hψ]
        <;> norm_num
  specialize h1 n
  exact_mod_cast h1