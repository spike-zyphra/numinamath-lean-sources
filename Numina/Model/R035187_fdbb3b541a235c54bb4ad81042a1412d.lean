import Mathlib
set_option linter.unusedVariables false

structure IntPoly where
  a : ℤ := 1  
  b : ℤ
  c : ℤ

def IntPoly.eval (p : IntPoly) (x : ℤ) : ℤ :=
  p.a * x^2 + p.b * x + p.c

def IntPoly.hasIntRoot (p : IntPoly) : Prop :=
  ∃ r : ℤ, IntPoly.eval p r = 0

def initialPoly : IntPoly :=
  { a := 1, b := 1, c := 2014 }

def calvinMove (p : IntPoly) (increase : Bool) : IntPoly :=
  if increase then
    { a := p.a, b := p.b + 1, c := p.c }
  else
    { a := p.a, b := p.b - 1, c := p.c }

def hobbesMove (p : IntPoly) (increase : Bool) : IntPoly :=
  if increase then
    { a := p.a, b := p.b, c := p.c + 1 }
  else
    { a := p.a, b := p.b, c := p.c - 1 }

def calvinStrategy (p : IntPoly) : Bool :=
  IntPoly.eval p 2 = 1 ∧ p.b < 0

def makeCalvinMove (p : IntPoly) : IntPoly :=
  calvinMove p (calvinStrategy p)

theorem algebra_607887 : 
  ∃ (s : IntPoly → Bool), 
    ∀ (hobbesStrategy : IntPoly → Bool),
    ∃ (i : ℕ), ∃ (p : IntPoly), 
      p.hasIntRoot ∧ 
      ∃ (p_prev : IntPoly), p = makeCalvinMove p_prev := by
  use fun _ => true
  intro h
  use 1 
  use { a := 1, b := -1, c := 0 }
  constructor 
  · -- Show the polynomial has integer roots
    use 0 
    all_goals norm_num [IntPoly.eval, IntPoly.hasIntRoot]
  · -- Show there exists a previous polynomial 
    use { a := 1, b := 0, c := 0 }
    have eq : makeCalvinMove { a := 1, b := 0, c := 0 } = { a := 1, b := -1, c := 0 } := by
      simp [calvinMove, makeCalvinMove, calvinStrategy, IntPoly.eval]
      <;> norm_num 
    rw [eq]
    all_goals norm_num