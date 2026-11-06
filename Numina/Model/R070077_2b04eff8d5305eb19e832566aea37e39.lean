import Mathlib

theorem algebra_19817 {p q : Polynomial ℝ} (hp : p.degree = 7) (hq : q.degree = 7) :
    (p * q).degree = 14 := by 
  have h1 : p ≠ 0 := by 
    by_contra h
    rw [h] at hp
    simp at hp
  have h2 : q ≠ 0 := by 
    by_contra h
    rw [h] at hq
    simp at hq
  have h3 : (p * q).degree = p.degree + q.degree := by 
    rw [Polynomial.degree_mul]
    all_goals try contradiction
    all_goals try tauto
  rw [h3, hp, hq]
  all_goals try { 
    try { 
      norm_num 
    }
    try { 
      nlinarith 
    }
  }
  <;> try { 
    simp 
    <;> try { 
      linarith 
    }
    <;> try { 
      nlinarith 
    }
  }
  all_goals try { 
    try { 
      native_decide 
    }
    <;> try { 
      nlinarith 
    }
  }
  all_goals try { 
    try { 
      native_decide 
    }
    <;> try { 
      nlinarith 
    }
  }
  <;> try { 
    omega 
  }
  all_goals try { 
    try { 
      native_decide 
    }
    <;> try { 
      nlinarith 
    }
  }
  all_goals try { 
    tauto 
  }