import Mathlib

theorem number_theory_315557 : ¬Finite ℚ := by 
  apply Infinite.not_finite
  all_goals
    try { 
      apply Countable.infinite
      <;> try { native_decide }
      all_goals try native_decide
      <;> try { native_decide }
    }
    all_goals try native_decide
    <;> try trivial
    <;> try { native_decide }