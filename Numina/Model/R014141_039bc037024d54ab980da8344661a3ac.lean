import Mathlib

theorem algebra_159254 {f : ℕ → ℤ} (hf : f 0 = 3 ∧ f 1 = 7 ∧ f 2 = 21 ∧ f 3 = 51)
    (h : ∃ p : Polynomial ℤ, p.degree = 3 ∧ ∀ n, f n = p.eval (n : ℤ)) :
    ∀ n, f n = n^3 + 2 * n^2 + n + 3 := by
  rcases hf with ⟨h0, h1, h2, h3⟩
  rcases h with ⟨p, hp_degree, hp⟩
  have eq1 : f 0 = p.eval (0 : ℤ) := hp 0
  rw [h0] at eq1
  have eq2 : f 1 = p.eval (1 : ℤ) := hp 1
  rw [h1] at eq2
  have eq3 : f 2 = p.eval (2 : ℤ) := hp 2
  rw [h2] at eq3
  have eq4 : f 3 = p.eval (3 : ℤ) := hp 3
  rw [h3] at eq4

  have eq1' : p.eval (0 : ℤ) = 3 := by linarith
  have eq2' : p.eval (1 : ℤ) = 7 := by linarith
  have eq3' : p.eval (2 : ℤ) = 21 := by linarith
  have eq4' : p.eval (3 : ℤ) = 51 := by linarith

  have eq5 : p.natDegree = 3 := by
    have h5 : p.degree = 3 := hp_degree
    rw [Polynomial.natDegree_eq_of_degree_eq_some h5]

  have eq1'' : p.eval (0 : ℤ) = p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, eq5, Finset.sum_range_succ]

  have eq2'' : p.eval (1 : ℤ) = p.coeff 0 + p.coeff 1 * (1 : ℤ) + p.coeff 2 * (1 : ℤ)^2 + p.coeff 3 * (1 : ℤ)^3 := by
    simp [Polynomial.eval_eq_sum_range, eq5, Finset.sum_range_succ]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    all_goals
      try linarith
      all_goals try { linarith }
      all_goals try { tauto }
      all_goals try { omega }
      all_goals try { linarith }
      all_goals try { 
        tauto
        all_goals linarith
      }
      all_goals try { 
        tauto
        all_goals linarith
      }
      all_goals try { 
        nlinarith
        all_goals try { 
          nlinarith
          all_goals try omega
        }
      }

  have eq3'' : p.eval (2 : ℤ) = p.coeff 0 + p.coeff 1 * (2 : ℤ) + p.coeff 2 * (2 : ℤ)^2 + p.coeff 3 * (2 : ℤ)^3 := by
    simp [Polynomial.eval_eq_sum_range, eq5, Finset.sum_range_succ]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    all_goals
      try linarith
      all_goals try { linarith }
      all_goals try { tauto }
      all_goals try { 
        nlinarith 
        all_goals try { 
          nlinarith
          all_goals try omega
        }
      }
      all_goals try { 
        omega
        all_goals try tauto
      }
      all_goals try { 
        tauto
        all_goals nlinarith
      }
 
  have eq4'' : p.eval (3 : ℤ) = p.coeff 0 + p.coeff 1 * (3 : ℤ) + p.coeff 2 * (3 : ℤ)^2 + p.coeff 3 * (3 : ℤ)^3 := by
    simp [Polynomial.eval_eq_sum_range, eq5, Finset.sum_range_succ]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    all_goals
      try linarith
      all_goals try { linarith }
      all_goals try { tauto }
      all_goals try { 
        nlinarith
        all_goals try { 
          nlinarith
          all_goals try omega
        }
      }
      all_goals try { 
        omega 
        all_goals try tauto
      }
      all_goals try { 
        tauto
        all_goals nlinarith
      }
      all_goals try { 
        nlinarith
        all_goals try { 
          nlinarith
          all_goals try omega
        }
        all_goals try omega
      }
  
  rw [eq1''] at eq1'
  rw [eq2''] at eq2'
  rw [eq3''] at eq3'
  rw [eq4''] at eq4'

  have co0 : p.coeff 0 = 3 := by linarith
  have co1 : p.coeff 1 = 1 := by
    nlinarith [eq1', eq2', eq3', eq4', co0]

  have co2 : p.coeff 2 = 2 := by
    nlinarith [eq1', eq2', eq3', eq4', co0, co1]

  have co3 : p.coeff 3 = 1 := by
    nlinarith [eq1', eq2', eq3', eq4', co0, co1, co2]

  intro n
  have eq6 : f n = p.eval (n : ℤ) := hp n
  rw [eq6]

  have eq7 : p.eval (n : ℤ) = p.coeff 0 + p.coeff 1 * (n : ℤ) + p.coeff 2 * (n : ℤ) ^ 2 + p.coeff 3 * (n : ℤ) ^ 3 := by
    simp [Polynomial.eval_eq_sum_range, eq5, Finset.sum_range_succ]
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    all_goals 
      try { 
        nlinarith 
        <;> try { 
          nlinarith 
          <;> try { 
            omega 
            <;> try { tauto }
          } 
        } 
      }
      <;> try { 
        omega 
        <;> try { tauto }
      }
      <;> try { 
        tauto 
        <;> try { omega }
      }
      all_goals try { 
        tauto 
        <;> try { omega }
      }
      all_goals try { 
        nlinarith 
        all_goals try { 
          omega 
          all_goals try tauto
        }
      }
 
  rw [eq7]
  simp only [co0, co1, co2, co3]
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num
  all_goals try { 
    nlinarith <;> try { 
      omega 
      <;> try { 
        tauto 
        <;> try { 
          tauto 
          <;> try { 
            omega 
            <;> try { 
              tauto <;> tauto
            } 
          }
        } 
      }
    }
    all_goals try { 
      nlinarith
      all_goals try { 
        omega <;> tauto
      }
    }
  }
  all_goals try { 
    omega 
    all_goals try tauto 
  }
  all_goals try { 
    tauto 
    all_goals nlinarith 
  }
  all_goals try { 
    nlinarith 
    all_goals try tauto 
    all_goals try { 
      tauto <;> try { 
        nlinarith <;> try { 
          tauto 
          <;> nlinarith
        }
      }
    }
  }
  all_goals try { 
    nlinarith
    all_goals try tauto
    all_goals try { 
      tauto 
      all_goals nlinarith 
    }
    all_goals try { 
      omega 
      all_goals tauto 
      all_goals nlinarith 
    }
  }