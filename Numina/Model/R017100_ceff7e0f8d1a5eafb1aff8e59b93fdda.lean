import Mathlib

def f (n : ℕ) : ℕ := match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => f n + f (n + 1)

theorem number_theory_584 :
    Set.ncard {n | n < 100 ∧ Even (f n)} = 33 := by
  have h4 : ∀ n : ℕ, Even (f n) ↔ n % 3 = 2 := by
    intro n
    have h : ∀ (n : ℕ), Even (f n) ↔ n % 3 = 2 := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        simp [f]
        <;> try { omega }
        <;> try native_decide
      | succ n =>
        cases n with
        | zero =>
          simp [f]
          <;> try { omega }
          <;> try native_decide
        | succ n =>
          cases n with
          | zero =>
            simp [f, Nat.even_iff, Nat.odd_iff]
            <;> try { native_decide }
            <;> try { tauto }
          | succ n =>
            have h1 := ih (n) (by linarith)
            have h2 := ih (n + 1) (by linarith)
            simp [f, Nat.even_iff, Nat.odd_iff] at h1 h2 ⊢
            omega
    exact h n

  have h1 : {n | n < 100 ∧ Even (f n)} = Finset.filter (fun n => n % 3 = 2) (Finset.Iio (100 : ℕ)) := by
    ext n
    simp [h4]
    <;> try { tauto }
    all_goals try { omega }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide