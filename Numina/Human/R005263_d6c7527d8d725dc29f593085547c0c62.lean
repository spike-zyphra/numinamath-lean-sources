import Mathlib

namespace algebra_607252

-- This seems not available in a non-tactic module of Mathlib.
theorem eq_mul_eq {α} [Mul α] {a b c d : α} (a_eq_c : a = c) (b_eq_d : b = d) : a * b = c * d := by
  rw [a_eq_c, b_eq_d]

abbrev X := Fin 3 → ℝ

namespace by_cyclic
variable (x : X)

abbrev CyclicEquationSystem := (i : Fin 3) →
    let a := x i
    let b := x (1 + i)
    let c := x (2 + i)
    a * (b ^ 2 + c) = c * (c + a * b)

lemma equationSystem_cyclic (cyclicEquationSystem : CyclicEquationSystem x) (j : Fin 3) : CyclicEquationSystem (x ∘ (. + j)) := by
  unfold CyclicEquationSystem at *
  simp at *
  intro i
  convert cyclicEquationSystem (i + j) using 0
  ring_nf

namespace mp
variable (cyclicEquationSystem : CyclicEquationSystem x)
include cyclicEquationSystem

-- 等式可以重新写成 $a b(b-c)=c(c-a)$, $b c(c-a)=a(a-b)$ 和 $\mathrm{ca}(\mathrm{a}-\mathrm{b})=\mathrm{b}(\mathrm{b}-\mathrm{c})$。
lemma h0 : let a := x 0; let b := x 1; let c := x 2
    a * b * (b - c) = c * (c - a) := by
  have := cyclicEquationSystem 0
  dsimp at this
  linarith
  --simp +arith +decide [this] -- doesn't work
  /-
  calc
    x 0 * x 1 * (x 1 - x 2) = x 0 * x 1 ^ 2 - x 0 * x 1 * x 2 := by ring
    _ = x 0 * x 1 ^ 2 + x 0 * x 2 - x 0 * x 2 - x 0 * x 1 * x 2 := by ring
    _ = x 0 * (x 1 ^ 2 + x 2) - x 0 * x 2 - x 0 * x 1 * x 2 := by ring
    _ = x 2 * (x 2 + x 0 * x 1) - x 0 * x 2 - x 0 * x 1 * x 2 := by congr
    _ = x 2 * (x 2 - x 0) := by ring
   -/

-- 将这三个等式相乘，得到 $(\mathrm{abc})^{2}(\mathrm{c}-\mathrm{a})(\mathrm{b}-\mathrm{c})(\mathrm{a}-\mathrm{b})=$ $\mathrm{abc}(\mathrm{c}-\mathrm{a})(\mathrm{b}-\mathrm{c})(\mathrm{a}-\mathrm{b})$。
lemma h1 : let a := x 0; let b := x 1; let c := x 2
    (a * b * c) ^ 2 * (b - c) * (c - a) * (a - b) = a * b * c * (b - c) * (c - a) * (a - b) := by
  have h0_0 := h0 x cyclicEquationSystem
  have h0_1 := h0 (x ∘ (. + 1)) (equationSystem_cyclic x cyclicEquationSystem 1)
  have h0_2 := h0 (x ∘ (. + 2)) (equationSystem_cyclic x cyclicEquationSystem 2)
  --simp at h0_0 h0_1 h0_2
  dsimp at *
  --nlinarith -- doesn't work
  have := eq_mul_eq (eq_mul_eq h0_0 h0_1) h0_2
  convert this using 1
  . ring
  . ring

lemma solution_a_eq_0 (a_eq_0 : x 0 = 0) : x 0 = x 1 ∧ x 1 = x 2 := by
  have c_eq_0 := by
    have := cyclicEquationSystem 0
    simp [a_eq_0] at this
    exact this
  have b_eq_0 := by
    have := cyclicEquationSystem 2
    simp [c_eq_0] at this
    exact this
  rw [a_eq_0, b_eq_0, c_eq_0]
  simp

lemma solution_b_eq_0 (b_eq_0 : x 1 = 0) : x 0 = x 1 ∧ x 1 = x 2 := by
  have := solution_a_eq_0 (x ∘ (. + 1)) (equationSystem_cyclic x cyclicEquationSystem 1) b_eq_0
  simp at this
  constructor <;> linarith

lemma solution_c_eq_0 (c_eq_0 : x 2 = 0) : x 0 = x 1 ∧ x 1 = x 2 := by
  have := solution_a_eq_0 (x ∘ (. + 2)) (equationSystem_cyclic x cyclicEquationSystem 2) c_eq_0
  simp at this
  constructor <;> linarith

lemma solution_a_eq_b (a_eq_b : x 0 = x 1) : x 0 = x 1 ∧ x 1 = x 2 := by
  let a := x 0; let b := x 1; let c := x 2
  have := h0 (x ∘ (. + 2)) (equationSystem_cyclic x cyclicEquationSystem 2)
  simp [a_eq_b] at this
  rcases this with h | h
  . exact solution_b_eq_0 x cyclicEquationSystem h
  . constructor <;> linarith

-- 若 $a b c=1$，此时 $a, b, c$ 都不为零。等式重新写为：$b-c=c^{2}(c-a)$, $c-a=a^{2}(a-b)$ 和 $a-b=b^{2}(b-c)$。
lemma abc_eq_1_implies_b_sub_c_same_sign_as_c_sub_a : let a := x 0; let b := x 1; let c := x 2
    a * b * c = 1 → (b - c ≥ 0 ∧ c - a ≥ 0) ∨ (b - c ≤ 0 ∧ c - a ≤ 0) := by
  intro a b c abc_eq_1
  have : b - c = c ^ 2 * (c - a) := by calc
    b - c = a * b * c * (b - c) := by rw [abc_eq_1]; simp
    _ = c * (a * b * (b - c)) := by ring
    _ = c * (c * (c - a)) := by congr 1; exact h0 x cyclicEquationSystem
    _ = c ^ 2 * (c - a) := by ring
  by_cases h : /- b - c -/ c - a ≥ 0
  . left
    constructor
    . nlinarith
    . linarith
  . right
    constructor
    . nlinarith
    . linarith

lemma solution : x 0 = x 1 ∧ x 1 = x 2 := by
  have := h1 x cyclicEquationSystem
  simp at this
  -- 特别地，有以下几种情况：
  rcases this with ⟨⟨h | h⟩ | h⟩ | h
  . let abc := x 0 * x 1 * x 2
    /-
    rw [show abc ^ 2 = abc * abc by ring] at h
    rw [show x 0 * x 1 * x 2 = abc from rfl] at h
    simp at h -- doesn't work
     -/
    have : abc = 0 ∨ abc = 1 :=
      eq_zero_or_one_of_sq_eq_self h -- `by simp` doesn't work here.
    rcases this with abc_eq_0 | abc_eq_1
    . -- - 若 $\mathrm{abc}=0$，由于等式是循环的，假设 $\mathrm{a}=0$。根据第一个等式 $\mathbf{c}^{2}=0$，因此 $\mathbf{c}=0$。根据第三个等式，$\boldsymbol{b}^{2}=0$，因此 $\mathrm{b}=0$。
      simp [abc] at abc_eq_0
      rcases abc_eq_0 with ⟨h | h⟩ | h
      . exact solution_a_eq_0 x cyclicEquationSystem h
      . exact solution_b_eq_0 x cyclicEquationSystem h
      . exact solution_c_eq_0 x cyclicEquationSystem h
    . -- - 若 $a b c=1$，此时 $a, b, c$ 都不为零。等式重新写为：$b-c=c^{2}(c-a)$, $c-a=a^{2}(a-b)$ 和 $a-b=b^{2}(b-c)$。特别地，$a-b$，$b-c$ 和 $c-a$ 同号，但和为零，因此必然有 $\mathrm{a}-\mathrm{b}=\mathrm{b}-\mathrm{c}=\mathrm{c}-\mathrm{a}=0$，即 $\mathrm{a}=\mathrm{b}=\mathrm{c}$。
      let a := x 0; let b := x 1; let c := x 2
      have bca_eq_1 : b * c * a = 1 := by
        convert abc_eq_1 using 1
        ring
      have cab_eq_1 : c * a * b = 1 := by
        convert abc_eq_1 using 1
        ring
      -- 特别地，$a-b$，$b-c$ 和 $c-a$ 同号，但和为零，因此必然有 $\mathrm{a}-\mathrm{b}=\mathrm{b}-\mathrm{c}=\mathrm{c}-\mathrm{a}=0$，即 $\mathrm{a}=\mathrm{b}=\mathrm{c}$。
      have same_sign_0 := abc_eq_1_implies_b_sub_c_same_sign_as_c_sub_a x cyclicEquationSystem abc_eq_1
      have same_sign_1 := abc_eq_1_implies_b_sub_c_same_sign_as_c_sub_a (x ∘ (. + 1)) (equationSystem_cyclic x cyclicEquationSystem 1) bca_eq_1
      have same_sign_2 := abc_eq_1_implies_b_sub_c_same_sign_as_c_sub_a (x ∘ (. + 2)) (equationSystem_cyclic x cyclicEquationSystem 2) cab_eq_1
      dsimp at same_sign_0 same_sign_1 same_sign_2
      cases same_sign_0 <;>
      . cases same_sign_1 <;>
        . cases same_sign_2 <;>
          . constructor <;>
            . nlinarith
  . have := solution_a_eq_b (x ∘ (. + 1)) (equationSystem_cyclic x cyclicEquationSystem 1) (show x 1 = x 2 by linarith)
    simp at this
    constructor <;> linarith
  . have := solution_a_eq_b (x ∘ (. + 2)) (equationSystem_cyclic x cyclicEquationSystem 2) (show x 2 = x 0 by linarith)
    simp at this
    constructor <;> linarith
  . -- - 若 $a, b, c$ 中有两个元素相等，假设 $a=b$。此时有 $b c(c-a)=0$。如果 $\mathrm{b}=0$ 或 $\mathrm{c}=0$，则回到前一种情况，否则 $\mathrm{a}=\mathrm{b}=\mathrm{c}$。
    exact solution_a_eq_b x cyclicEquationSystem (by linarith)

end mp

namespace mpr
variable (solution : x 0 = x 1 ∧ x 1 = x 2)
include solution

lemma cyclicEquationSystem : CyclicEquationSystem x := by
  unfold CyclicEquationSystem
  have any_x_eq_x_0 i : x i = x 0 := by
    have := solution
    rcases this
    fin_cases i <;>
    . dsimp <;>
      linarith
  --dsimp
  intro i
  rw [any_x_eq_x_0 i, any_x_eq_x_0 (1 + i), any_x_eq_x_0 (2 + i)]
  --dsimp
  ring

end mpr
end by_cyclic

/- Trouver tous les triplets de réels ( $\mathrm{a}, \mathrm{b}, \mathrm{c}$ ) vérifiant le système d'égalités :

$$
\left\{\begin{array}{l}
a\left(b^{2}+c\right)=c(c+a b) \\
b\left(c^{2}+a\right)=a(a+b c) \\
c\left(a^{2}+b\right)=b(b+a c)
\end{array}\right.
$$ -/
theorem algebra_607252 (a b c : ℝ) :
    a * (b ^ 2 + c) = c * (c + a * b) ∧ b * (c ^ 2 + a) = a * (a + b * c) ∧ c * (a ^ 2 + b) = b * (b + a * c) ↔
    a = b ∧ b = c := by
  let x : X := fun | 0 => a | 1 => b | 2 => c
  constructor
  . intro equationSystem
    exact by_cyclic.mp.solution x (
      fun
      | 0 => equationSystem.1
      | 1 => equationSystem.2.1
      | 2 => by
        have := equationSystem.2.2
        dsimp
        linarith
    )
  . intro solution
    have cyclicEquationSystem := by_cyclic.mpr.cyclicEquationSystem x solution
    have := cyclicEquationSystem 0
    have := cyclicEquationSystem 1
    have := cyclicEquationSystem 2
    dsimp [x] at *
    constructor
    . assumption
    . constructor
      . assumption
      . linarith

end algebra_607252
open algebra_607252
