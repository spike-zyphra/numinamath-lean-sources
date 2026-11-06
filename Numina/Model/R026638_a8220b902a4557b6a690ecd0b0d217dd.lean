import Mathlib

theorem number_theory_8952 (S : Finset ℤ) (hS : S = {-9, 3, 9, 11, 59}) :
    S.card = 5 ∧ ∀ T ⊆ S, T.card = 3 → Prime (∑ x ∈ T, x) := by
  constructor
  · -- Show the card of S is 5
    rw [hS]
    native_decide
  · -- Show any 3-element subset sum is prime
    intro T hT hT3
    rw [show S = {-9, 3, 9, 11, 59} by exact hS] at hT
    have h1 : T ⊆ ({-9, 3, 9, 11, 59} : Finset ℤ) := hT
    have h3 : T.card = 3 := hT3
    have h4 : T ∈ (Finset.filter (fun s => s.card = 3) (Finset.powerset ({-9, 3, 9, 11, 59} : Finset ℤ))) := by 
      simp [Finset.mem_powerset, h1, Finset.mem_filter, h3]
      <;> tauto
    fin_cases h4 
    <;> try { 
      simp_all [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton] 
      <;> native_decide 
      <;> try { 
        tauto 
        <;> try { contradiction } 
      }
    }
    <;> try { 
      contradiction 
    }
    <;> try { 
      tauto 
      <;> try { contradiction } 
    }
    <;> try { 
      contradiction 
    }
    <;> try { 
      tauto 
      <;> try { contradiction } 
    }
    <;> try { 
      contradiction 
    }
    <;> try { 
      tauto 
      <;> try { contradiction } 
    }
    <;> try { 
      contradiction 
    }
    <;> try { 
      tauto 
      <;> try { contradiction } 
    }
    <;> try { 
      contradiction 
    }
    <;> try { 
      tauto 
      <;> try { contradiction } 
    }
    <;> try { 
      contradiction 
    }
    <;> try { 
      tauto 
      <;> try { contradiction } 
    }
    <;> try { 
      contradiction 
    }