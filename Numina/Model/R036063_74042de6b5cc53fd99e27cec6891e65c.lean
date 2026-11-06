import Mathlib


open Set


theorem algebra_97330 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 2017 ∧ ∃ k : ℕ, (1 + n + (n ^ 2) / 2 + (n ^ 3) / 6 + (n ^ 4) / 24 + (n ^ 5) / 120 + (n ^ 6) / 720 : ℚ) = k} = 134 := by
  have h2 : {n : ℕ | 0 < n ∧ n < 2017 ∧ ∃ k : ℕ, (1 + n + (n ^ 2) / 2 + (n ^ 3) / 6 + (n ^ 4) / 24 + (n ^ 5) / 120 + (n ^ 6) / 720 : ℚ) = k} = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 2017 ∧ (⌊(1 + n + (n ^ 2) / 2 + (n ^ 3) / 6 + (n ^ 4) / 24 + (n ^ 5) / 120 + (n ^ 6) / 720 : ℚ)⌋₊ = (1 + n + (n ^ 2) / 2 + (n ^ 3) / 6 + (n ^ 4) / 24 + (n ^ 5) / 120 + (n ^ 6) / 720 : ℚ))) (Finset.Icc 0 2016) := by 
    ext n
    simp
    <;> try { 
      omega 
    }
    <;> try { 
      aesop 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        tauto 
      }
    }
    <;> try { 
      intro h
      rcases h with ⟨h_pos, h_lt, h3⟩
      have h4 : n ≤ 2016 := by linarith 
      simp_all 
      <;> try { 
        tauto 
      }
      <;> try { 
        nlinarith 
      }
    }
    <;> try { 
      omega 
      <;> tauto 
    }
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide