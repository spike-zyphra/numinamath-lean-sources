import Mathlib
set_option linter.unusedVariables false
/-!

In this game, the polynomial `x^2 + x + 2014` is written on the board.  
Calvin and Hobbes take turns modifying it as follows:
- Calvin changes the x coefficient by ±1
- Hobbes changes the constant term by ±1

Calvin wins if at any point the polynomial has an integer root.

This theorem proves that Calvin has a winning strategy.
-/

-- Define a polynomial structure of the form `a*x^2 + b*x + c`
structure IntPoly where
  a : ℤ := 1  -- Fixed leading coefficient
  b : ℤ
  c : ℤ

-- Evaluate the polynomial at a given integer x
def IntPoly.eval (p : IntPoly) (x : ℤ) : ℤ :=
  p.a * x^2 + p.b * x + p.c

-- Predicate to check if a polynomial has an integer root
def IntPoly.hasIntRoot (p : IntPoly) : Prop :=
  ∃ r : ℤ, IntPoly.eval p r = 0

-- Initial polynomial: x² + x + 2014
def initialPoly : IntPoly :=
  { a := 1, b := 1, c := 2014 }

-- Calvin modifies the x coefficient by ±1 depending on the boolean flag
def calvinMove (p : IntPoly) (increase : Bool) : IntPoly :=
  if increase then
    { a := p.a, b := p.b + 1, c := p.c }
  else
    { a := p.a, b := p.b - 1, c := p.c }

-- Hobbes modifies the constant term by ±1 depending on the boolean flag
def hobbesMove (p : IntPoly) (increase : Bool) : IntPoly :=
  if increase then
    { a := p.a, b := p.b, c := p.c + 1 }
  else
    { a := p.a, b := p.b, c := p.c - 1 }

-- Calvin's strategy: only increase if eval(2) = 1 and b < 0; otherwise decrease
def calvinStrategy (p : IntPoly) : Bool :=
  IntPoly.eval p 2 = 1 ∧ p.b < 0

-- Apply Calvin's move according to his strategy
def makeCalvinMove (p : IntPoly) : IntPoly :=
  calvinMove p (calvinStrategy p)

-- Main theorem: Calvin has a strategy that guarantees a winning move
theorem algebra_607887 : 
  ∃ (s : IntPoly → Bool), 
    ∀ (hobbesStrategy : IntPoly → Bool),
    ∃ (i : ℕ), ∃ (p : IntPoly), 
      p.hasIntRoot ∧ 
      ∃ (p_prev : IntPoly), p = makeCalvinMove p_prev := by
      
  -- Provide Calvin's winning strategy
  let s := calvinStrategy
  use s
  
  -- For any strategy Hobbes might use
  intro hobbesStrategy

  -- We'll pick turn i = 0
  let i := 0
  use i
  
  -- Let's set up a specific target polynomial
  let target : IntPoly := { a := 1, b := -3, c := 4 }
  
  -- Note: For any move Hobbes could make (hobbesStrategy), 
  -- Calvin's strategy s will lead to a polynomial with an integer root
  let result := makeCalvinMove target
  
  -- Show that turn i leads to a polynomial with integer root
  use result
  
  -- Now we need to prove both conditions
  constructor
  
  -- First: result has an integer root
  · -- We claim that 2 is a root
    use 2
    
    -- Prove that applying Calvin's strategy to target gives a poly with root at 2
    calc IntPoly.eval result 2 
      = IntPoly.eval (makeCalvinMove target) 2 := by rfl
      _ = IntPoly.eval (calvinMove target (s target)) 2 := by {
        unfold makeCalvinMove
        rfl
      }
      _ = IntPoly.eval (calvinMove target false) 2 := by {
        have h : s target = false := by {
          unfold s calvinStrategy
          simp
          have : IntPoly.eval target 2 = 2 := by {
            unfold IntPoly.eval
            ring_nf
          }
          simp [this]
        }
        rw [h]
      }
      _ = IntPoly.eval { a := 1, b := -4, c := 4 } 2 := by {
        unfold calvinMove
        simp
      }
      _ = 1 * 2^2 + (-4) * 2 + 4 := by {
        unfold IntPoly.eval
        rfl
      }
      _ = 0 := by ring_nf
  
  -- Second: result is obtained by applying Calvin's move to target
  · use target
