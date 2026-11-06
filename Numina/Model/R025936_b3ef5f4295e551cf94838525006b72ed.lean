import Mathlib

def isPrimitiveRoot (p : ℕ) (n : ZMod p) : Prop :=
  ∀ x : ZMod p, x ≠ 0 → ∃ m : ℕ, n ^ m = x

theorem number_theory_6542 : isPrimitiveRoot 23 5 := by
  intro x hx
  have h1 : x ≠ 0 := hx
  fin_cases x <;> simp [isPrimitiveRoot] at *
  <;> try { 
    use 0; all_goals native_decide
  }
  <;> try { 
    use 1; all_goals native_decide
  }
  <;> try { 
      use 2; all_goals native_decide
    }
  <;> try { 
      use 3; all_goals native_decide
    }
  <;> try { 
      use 4; all_goals native_decide
    }
  <;> try { 
      use 5; all_goals native_decide
    }
  <;> try { 
      use 6; all_goals native_decide
    }
  <;> try { 
      use 7; all_goals native_decide
    }
  <;> try { 
    use 8; all_goals native_decide
  }
  <;> try { 
      use 9; all_goals native_decide
    }
  <;> try { 
      use 10; all_goals native_decide
    }
  <;> try { 
    use 11; all_goals native_decide
  }
  <;> try { 
    use 12; all_goals native_decide
  }
  <;> try { 
      use 13; all_goals native_decide
    }
  <;> try { 
      use 14; all_goals native_decide
    }
  <;> try { 
      use 15; all_goals native_decide
    }
  <;> try { 
      use 16; all_goals native_decide
    }
  <;> try { 
      use 17; all_goals native_decide
    }
  <;> try { 
      use 18; all_goals native_decide
    }
  <;> try { 
      use 19; all_goals native_decide
    }
  <;> try { 
    use 20; all_goals native_decide
  }
  <;> try { 
      use 21; all_goals native_decide
    }
  <;> try { 
      use 22; all_goals native_decide
    }