import Mathlib

theorem number_theory_225863_1 (n : ℕ) (hn : 0 < n) :
    Set.Infinite {(a, b, c) : ℕ × ℕ × ℕ | a ^ n + b ^ n = c ^ (n + 1)} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (x : ℕ) => (0, (x) ^ (n + 1), (x) ^ n))
  · -- Show f is injective
    intro x y h
    simp [Prod.ext_iff] at h
    all_goals
      linarith
  · -- Show that all elements in the image of f satisfy the equation
    intro x
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      <;> norm_num
      all_goals
        linarith

theorem number_theory_225863_2 (m n : ℕ) (hn : 0 < n) (hm : 0 < m) (hcoprime : Nat.Coprime m n) :
    Set.Infinite {(a, b, c) : ℕ × ℕ × ℕ | a ^ n + b ^ n = c ^ m} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (x : ℕ) => (0, (x) ^ (m), (x) ^ (n)))
  · -- Show f is injective
    intro x y h
    have h1 : x ^ m = y ^ m := by
      simp [Prod.ext_iff] at h 
      tauto
    have h2 : x ^ n = y ^ n := by
      simp [Prod.ext_iff] at h 
      tauto
    -- Since m > 0, from x^m = y^m we get x = y
    have h3 : x = y := by
      have h4 : x ^ m = y ^ m := h1
      exact Nat.pow_left_injective (by linarith) h4
    exact h3
  · -- Show that all elements in the image of f satisfy the equation
    intro x
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      <;> norm_num
      all_goals
        linarith
  all_goals try linarith
  all_goals try { 
    tauto 
    <;> try { try { tauto <;> exfalso <;> tauto } }
  }
  all_goals try tauto
  all_goals try exfalso <;> try { contradiction }
  <;> try tauto
  <;> try { 
    tauto 
    <;> try { tauto <;> exfalso <;> tauto } <;> try { tauto <;> exfalso }
  }
  <;> try tauto
  <;> try { 
    tauto 
    <;> try { 
      tauto 
      <;> try { exfalso <;> tauto } <;> try { 
        exfalso 
        <;> tauto 
      }
    } 
  }
  <;> try tauto
  <;> try { tauto <;> exfalso <;> omega }
  <;> try tauto
  <;> try tauto <;> try { 
    exfalso 
    <;> try { 
      -- try { exfalso <;> tauto } <;> try { tauto <;> exfalso }
      exfalso <;> tauto 
    }
    <;> try { 
      tauto 
      <;> try { exfalso <;> tauto } 
    }
  }
  <;> try tauto
  <;> tauto
  <;> try { 
    exfalso 
    <;> try { contradiction } <;> try { exfalso <;> tauto }
  }
  <;> tauto
  <;> try tauto
  <;> try { exfalso <;> tauto }
  <;> try { contradiction }
  <;> try tauto
  <;> try { 
    tauto 
    <;> try { 
      exfalso 
      <;> try { contradiction } <;> try { exfalso <;> tauto } <;> try { contradiction }
    }
  }
  <;> try { 
    exfalso 
    <;> try { contradiction } <;> try { 
      exfalso 
      <;> try { contradiction } <;> try { tauto } <;> try { contradiction }
    } <;> try { contradiction }
  }
  <;> try { 
    exfalso 
    <;> try { contradiction } <;> try { contradiction }
  }
  <;> try { contradiction }
  <;> try { exfalso <;> tauto }
  <;> try { contradiction <;> try { exfalso <;> tauto } }
  <;> try { contradiction }
  <;> try { 
    tauto 
    <;> try { 
      exfalso <;> try { contradiction } <;> try { tauto } <;> try { contradiction }
    } <;> try { contradiction } <;> try { tauto } 
  }
  <;> try { 
    exfalso <;> try { contradiction } <;> try { tauto } <;> try { contradiction }
  }
  all_goals try tauto
  <;> try { 
    exfalso 
    <;> try { contradiction } <;> try { tauto } <;> try { contradiction }
  }
  <;> try tauto
  <;> try { 
    exfalso <;> try { tauto } <;> try { contradiction } <;> try { tauto }
  }
  all_goals try tauto
  <;> try { 
    exfalso 
    <;> try { contradiction } <;> try { contradiction } <;> try { contradiction }
  }
  <;> try { tauto <;> exfalso <;> tauto }