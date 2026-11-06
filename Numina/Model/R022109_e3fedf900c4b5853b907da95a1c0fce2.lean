import Mathlib

theorem number_theory_155454 (n : ℕ) (h₀ : n.Prime) (h₁ : n < 100) (h₂ : n > 9)
    (h₃ : (Nat.digits 10 n).sum = 10) :
    ∃! k, n - 18 * k ∈ Finset.Icc 10 20 := by
  interval_cases n <;> norm_num at h₀ h₁ h₂ h₃ ⊢ <;> try { 
    try { 
      use 0
      all_goals 
        simp_all [Finset.mem_Icc, Nat.succ_eq_add_one, Nat.le_of_lt]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
    }
    <;> try { 
      use 1
      all_goals 
        simp_all [Finset.mem_Icc, Nat.succ_eq_add_one, Nat.le_of_lt]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
    }
    <;> try { 
      use 3
      all_goals 
        simp_all [Finset.mem_Icc, Nat.succ_eq_add_one, Nat.le_of_lt]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
    }
    <;> try { 
      use 0
      all_goals 
        simp [Finset.mem_Icc]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
        <;> try { native_decide }
    }
    <;> try { 
      use 1 
      all_goals 
        simp [Finset.mem_Icc]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
        <;> try { native_decide }
    }
    <;> try { 
      use 2 
      all_goals 
        simp [Finset.mem_Icc]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
        <;> try { native_decide }
    }
    <;> try { 
      use 3 
      all_goals 
        simp [Finset.mem_Icc]
        <;> try { native_decide }
        <;> try { omega }
        <;> try { tauto }
        <;> try { native_decide }
    }
  }
  <;> norm_num at h₀ h₁ h₂ h₃ ⊢
  <;> native_decide