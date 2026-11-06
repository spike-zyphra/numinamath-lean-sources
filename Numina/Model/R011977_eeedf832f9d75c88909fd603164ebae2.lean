import Mathlib

def lemma_1 {x y : ℤ} : 121 ∣ x ^ 2 + y ^ 2 ↔ 11 ∣ x ∧ 11 ∣ y := by
  constructor
  . intro h
    
    have inst : Fact (Nat.Prime 11) := ⟨by decide⟩
    
    have h₁ : legendreSym 11 (-1) = -1 := by
      simp [legendreSym.at_neg_one (show 11 ≠ 2 by simp)]
    
    have h₂ : ↑(11 : ℕ) ∣ x ^ 2 + y ^ 2 := dvd_trans (by norm_num) h
    
    have H := legendreSym.prime_dvd_of_eq_neg_one (p := 11) (a := -1) h₁ (x := x) (y := y) (by simpa)
    simpa using H
  . 
    rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    ring_nf
    exact dvd_add (Int.dvd_mul_left (a ^ 2) 121) (Int.dvd_mul_left (b ^ 2) 121)

theorem number_theory_605979 :
    Set.ncard {n : ℤ | ∃ x y, n = x^2 + y^2 ∧ 1 ≤ x ∧ x ≤ 1000 ∧ 1 ≤ y ∧ y ≤ 1000 ∧ 121 ∣ n} = 3009 := by
  have h1 : {n : ℤ | ∃ x y, n = x ^ 2 + y ^ 2 ∧ 1 ≤ x ∧ x ≤ 1000 ∧ 1 ≤ y ∧ y ≤ 1000 ∧ 121 ∣ n} = Finset.image (fun p : ℤ × ℤ => (p.1) ^ 2 + (p.2) ^ 2) (Finset.filter (fun p : ℤ × ℤ => 121 ∣ (p.1 ^ 2 + p.2 ^ 2) ∧ 1 ≤ p.1 ∧ p.1 ≤ 1000 ∧ 1 ≤ p.2 ∧ p.2 ≤ 1000) ((Finset.Icc (1 : ℤ) 1000) ×ˢ (Finset.Icc (1 : ℤ) 1000))) := by 
    ext n
    simp 
    <;> 
    try { 
      aesop 
    }
    <;> 
    try { 
      simp [lemma_1] 
    }
  rw [h1] 
  rw [Set.ncard_coe_Finset]
  native_decide