import Mathlib

theorem algebra_180404 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : n % 10 = 5) :
    (n / 10) * (n / 10 + 1) * 100 + 25 = n ^ 2 := by 
  interval_cases n <;> omega
  <;> try { ring_nf <;> omega }
  all_goals try { 
    interval_cases n <;> omega 
    <;> try { 
      try { 
        ring_nf <;> omega 
        <;> tauto <;> nlinarith 
        <;> ring_nf <;> nlinarith 
      }
      <;> try { 
        omega 
        <;> try { 
          nlinarith 
          <;> tauto
        }
      }
    }
  }
  <;> try { 
    interval_cases n <;> ring_nf <;> omega
  }
  all_goals try { 
    omega
    <;> nlinarith 
    <;> try { 
      interval_cases n <;> ring_nf <;> tauto 
    }
    <;> try tauto 
    <;> try { 
      interval_cases n <;> ring_nf <;> omega 
      <;> tauto 
    }
    <;> try nlinarith 
    <;> try { 
      interval_cases n <;> ring_nf <;> omega 
      <;> tauto 
    }
  }
  all_goals try { 
    interval_cases n <;> ring_nf <;> try { 
      omega <;> tauto <;> nlinarith <;> omega 
    }
    <;> try { 
      omega 
      <;> try { 
        nlinarith <;> tauto
      }
    }
    <;> try { 
      omega 
      <;> try { 
        nlinarith <;> tauto 
      }
    }
    <;> try { 
      omega <;> try { 
        nlinarith <;> tauto 
      }
      <;> tauto 
    }
  }
  <;> try { 
    interval_cases n <;> try { 
      omega 
      <;> try { 
        nlinarith <;> tauto 
      }
    }
    <;> try { 
      omega 
      <;> try { 
        nlinarith <;> tauto 
      }
    }
    <;> try { 
      omega <;> try { 
        nlinarith <;> tauto 
      }
    }
  }
  all_goals try { 
    omega <;> try { 
      interval_cases n <;> try { 
        omega <;> try { 
          nlinarith <;> tauto <;> nlinarith <;> tauto
        }
      }
    }
  }