import Mathlib

open Set Real

/- Let $a, b, c$ be positive real numbers, find the minimum value of $\frac{a+3 c}{a+2 b+c}+\frac{4 b}{a+b+2 c}-\frac{8 c}{a+b+3 c}$.
(2004 Girls' Mathematical Olympiad) -/
namespace algebra_258818

def S : Set ℝ := { x | ∃ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ x = (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) } -- The set of all possible values of the expression

end algebra_258818

open algebra_258818

theorem algebra_258818 : IsLeast S (-17 + 12 * √2) := by
  dsimp[IsLeast]
  constructor

  case right =>
    dsimp[lowerBounds]
    
    have abc_lb (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) ≥ -17 + 12 * √2 := by
      -- Let $x=a+2 b+c, y=a+b+2 c, z=a+b+3 c$.
      let x := a + 2 * b + c
      let y := a + b + 2 * c
      let z := a + b + 3 * c

      -- By solving the equations above, we have $a+3 c=2 y-x$, $b=z+x-2 y, c=z-y$.
      have eq1 : a + 3 * c = 2 * y - x := by
        dsimp [x, y]
        linarith
    
      have eq2 : b = z + x - 2 * y := by
        dsimp [x, y, z]
        linarith

      have eq3 : c = z - y := by
        dsimp [y, z]
        linarith

      have xeq : x = a + 2 * b + c := by dsimp[x]
      have yeq : y = a + b + 2 * c := by dsimp[y]
      have zeq : z = a + b + 3 * c := by dsimp[z]

      have xpos : 0 < x := by 
        dsimp [x]
        linarith

      have ypos : 0 < y := by 
        dsimp [y]
        linarith

      have zpos : 0 < z := by 
        dsimp [z]
        linarith

      have xnzero : x ≠ 0 := ne_of_gt xpos
      have ynzero : y ≠ 0 := ne_of_gt ypos
      have znzero : z ≠ 0 := ne_of_gt zpos

      -- Therefore the target expression equals to $$ \begin{array}{c} \frac{2 y-x}{x}+\frac{4(z+x-2 y)}{y}-\frac{8(z-y)}{z}=-17+2 \frac{y}{x}+4 \frac{x}{y}+4 \frac{z}{y}+8 \frac{y}{z} \ \geqslant-17+2 \sqrt{8}+2 \sqrt{32}=-17+12 \sqrt{2} \end{array} $$
    
      have target_simp1 : (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) = -17 + 2 * (y / x) + 4 * (x / y) + 4 * (z / y) + 8 * (y / z) := by 
        rw [←xeq, ←yeq, ←zeq, eq1, eq2, eq3]
        rw [sub_div, mul_sub, mul_sub, sub_div, sub_div]
        simp [add_sub, ←sub_add, ←mul_div]
        simp [mul_add, add_div, ←add_assoc, ←mul_assoc]
        simp [div_self xnzero, div_self ynzero, div_self znzero]
        simp [←sub_add_eq_add_sub]
        norm_num
        rw [sub_eq_neg_add, sub_eq_neg_add, sub_eq_neg_add]
        simp [←add_assoc]
        norm_num
        linarith

      have sqrt_eight : √8 = 2 * √2 := by
        calc
        √8 = √(2 ^ 2 * 2) := by norm_num
        _ = √(2 ^ 2) * √2 := by rw [Real.sqrt_mul]; simp;
        _ = 2 * √2 := by rw [Real.sqrt_sq]; simp

      have sqrt_thirty_two : √32 = 4 * √2 := by
        calc
        √32 = √(4 ^ 2 * 2) := by norm_num
        _ = √(4 ^ 2) * √2 := by rw [Real.sqrt_mul]; simp;
        _ = 4 * √2 := by rw [Real.sqrt_sq]; simp

      have target_lb : (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) ≥ -17 + 2 * √8 + 2 * √32 := by
        rw [target_simp1]

        have hw1 : 0 ≤ (1 / 2 : ℝ) := by linarith
        have hw : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num

        have : 2 * √8 + 2 * √32 ≤ 2 * (y / x) + 4 * (x / y) + 4 * (z / y) + 8 * (y / z) := by
          have le1 : 2 * √8 ≤ 2 * (y / x) + 4 * (x / y) := by
            have : (4 : ℝ) = (2 : ℝ) * (2 : ℝ) := by norm_num
            rw [this, mul_assoc, ←mul_add]
            simp
            have hp1 : 0 ≤ (y / x : ℝ) := le_of_lt (div_pos ypos xpos)
            have hp2 : 0 ≤ (2 * (x / y) : ℝ) := le_of_lt (mul_pos two_pos (div_pos xpos ypos))
            have le1_1 := geom_mean_le_arith_mean2_weighted hw1 hw1 hp1 hp2 hw
            rw [←sqrt_eq_rpow, ←sqrt_eq_rpow] at le1_1
            rw [←(sqrt_mul hp1)] at le1_1
            rw [←mul_assoc] at le1_1
            rw [mul_comm (y / x)] at le1_1
            rw [mul_assoc, mul_div] at le1_1
            rw [div_mul y x, div_self, div_one, div_self] at le1_1
            norm_num at le1_1
            rw [←mul_add] at le1_1
            rw [←mul_div_right_comm, one_mul] at le1_1
            rw [le_div_iff₀'] at le1_1
            rwa [←sqrt_eight] at le1_1
            exact two_pos
            exact ynzero
            exact xnzero
          have le2 : 2 * √32 ≤ 4 * (z / y) + 8 * (y / z) := by
            have hp3 : 0 ≤ (4 * (z / y) : ℝ) := by
              apply le_of_lt
              apply mul_pos
              linarith
              exact div_pos zpos ypos
            have hp4 : 0 ≤ (8 * (y / z) : ℝ) := by
              apply le_of_lt
              apply mul_pos
              linarith
              exact div_pos ypos zpos
            have le2_1 := geom_mean_le_arith_mean2_weighted hw1 hw1 hp3 hp4 hw
            rw [←sqrt_eq_rpow, ←sqrt_eq_rpow] at le2_1
            rw [←(sqrt_mul hp3)] at le2_1
            rw [←mul_assoc, mul_assoc 4 (z / y)] at le2_1
            rw [mul_comm (z / y)] at le2_1
            rw [←mul_assoc] at le2_1
            norm_num at le2_1
            rw [mul_assoc 32, mul_div] at le2_1
            rw [div_mul, div_self, div_one, div_self, mul_one] at le2_1
            rw [←mul_add] at le2_1
            rw [←mul_div_right_comm, one_mul] at le2_1
            rw [le_div_iff₀'] at le2_1
            exact le2_1
            exact two_pos
            exact znzero
            exact ynzero
          rw [add_assoc (2 * (y / x) + 4 * (x / y))]
          apply add_le_add le1 le2
        rw [add_assoc (-17 : ℝ), add_assoc (-17 : ℝ), add_assoc (-17 : ℝ), add_assoc (-17 : ℝ)]
        apply add_le_add
        linarith
        assumption
        
      have target_lb_simp : (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) ≥ -17 + 12 * √2 := by
        have : -17 + 2 * √8 + 2 * √32 = -17 + 12 * √2 := by 
          rw [sqrt_eight, sqrt_thirty_two]
          ring_nf
        rw [←this]
        exact target_lb

      exact target_lb_simp
    intros s hs
    obtain ⟨a, b, c, ha, hb, hc, h⟩ := hs
    rw [h]
    exact abc_lb a b c ha hb hc
  
  case left =>
    -- It's trivial that the equality holds when $y=\sqrt{2} x, z=2 x$. Thus, when $b=(1+\sqrt{2}) a, c=(4+3 \sqrt{2}) a, a \in \mathbf{R}^{+}$, the target expression would yield its minimum value, $-17+12 \sqrt{2}$.

    have abc_min (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : b = (1 + √2) * a → c = (4 + 3 * √2) * a → (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) = -17 + 12 * √2 := by
      intro eq7 eq8

      have ne1 : 7 - 5 * √2 ≠ 0 := by 
        by_contra! hc
        have : 7 = 5 * √2 := by
          have := eq_add_of_sub_eq hc
          simp at this
          exact this
        have temp : 7^2 = (5 * √2)^2 := by rw[this]
        norm_num at temp
        rw [pow_two (5 * √2)] at temp
        have : (49 : ℝ) = 50 := by
          calc
          49 = 5 * √2 * (5 * √2) := by rw [temp]
          _ = 25 * (√2 * √2) := by ring_nf
          _ = 25 * 2 := by rw [←(sqrt_mul zero_le_two), sqrt_mul_self zero_le_two]
          _ = 50 := by norm_num
        linarith
      have ne2 : 10 - 7 * √2 ≠ 0 := by
        by_contra! hc
        have : 10 = 7 * √2 := by
          have := eq_add_of_sub_eq hc
          simp at this
          exact this
        have temp : 10^2 = (7 * √2)^2 := by rw[this]
        norm_num at temp
        rw [pow_two (7 * √2)] at temp
        have : (100 : ℝ) = 98 := by
          calc
          100 = 7 * √2 * (7 * √2) := by rw [temp]
          _ = 49 * (√2 * √2) := by ring_nf
          _ = 49 * 2 := by rw [←(sqrt_mul zero_le_two), sqrt_mul_self zero_le_two]
          _ = 98 := by norm_num
        linarith
        
      rw [eq7, eq8]
      calc
      (a + 3 * ((4 + 3 * √2) * a)) / (a + 2 * ((1 + √2) * a) + (4 + 3 * √2) * a) + 4 * ((1 + √2) * a) / (a + (1 + √2) * a + 2 * ((4 + 3 * √2) * a)) - 8 * ((4 + 3 * √2) * a) / (a + (1 + √2) * a + 3 * ((4 + 3 * √2) * a)) = (a + 3 * 4 * a + 3 * 3 * √2 * a) / (a + 2 * a + 2 * √2 * a + 4 * a + 3 * √2 * a) + (4 * a + 4 * √2 * a) / (a + a + √2 * a + 2 * 4 * a + 2 * 3 * √2 * a) - (8 * 4 * a + 8 * 3 * √2 * a) / (a + a + √2 * a + 3 * 4 * a + 3 * 3 * √2 * a) := by ring_nf
      _ = (13 + 9 * √2) * a / ((7 + 5 * √2) * a) + (4 + 4 * √2) * a / ((10 + 7 * √2) * a) - (32 + 24 * √2) * a / ((14 + 10 * √2) * a) := by ring_nf
      _ = (13 + 9 * √2) / (7 + 5 * √2) + (4 + 4 * √2) / (10 + 7 * √2) - (32 + 24 * √2) / (14 + 10 * √2) := by rw [mul_div_mul_right (13 + 9 * √2) (7 + 5 * √2) (ne_of_gt ha), mul_div_mul_right (4 + 4 * √2) (10 + 7 * √2) (ne_of_gt ha), mul_div_mul_right (32 + 24 * √2) (14 + 10 * √2) (ne_of_gt ha)]
      _ = (13 + 9 * √2) / (7 + 5 * √2) + (4 + 4 * √2) / (10 + 7 * √2) - (16 + 12 * √2) * 2 / ((7 + 5 * √2) * 2) := by ring_nf
      _ = (13 + 9 * √2) / (7 + 5 * √2) + (4 + 4 * √2) / (10 + 7 * √2) - (16 + 12 * √2) / (7 + 5 * √2) := by rw [mul_div_mul_right (16 + 12 * √2) (7 + 5 * √2) two_ne_zero]
      _ = ((13 + 9 * √2) - (16 + 12 * √2)) / (7 + 5 * √2) + (4 + 4 * √2) / (10 + 7 * √2) := by ring_nf
      _ = (-3 - 3 * √2) / (7 + 5 * √2) + (4 + 4 * √2) / (10 + 7 * √2) := by ring_nf
      _ = (-3 - 3 * √2) * (7 - 5 * √2) / ((7 + 5 * √2) * (7 - 5 * √2)) + (4 + 4 * √2) * (10 - 7 * √2) / ((10 + 7 * √2) * (10 - 7 * √2)) := by rw [←mul_div_mul_right (-3 - 3 * √2) (7 + 5 * √2) ne1, ←mul_div_mul_right (4 + 4 * √2) (10 + 7 * √2) ne2]
      _ = (-3 - 3 * √2) * (7 - 5 * √2) / (49 - 25 * (√2 * √2)) + (4 + 4 * √2) * (10 - 7 * √2) / (100 - 49 * (√2 * √2)) := by ring_nf
      _ = (-3 - 3 * √2) * (7 - 5 * √2) / (49 - 25 * 2) + (4 + 4 * √2) * (10 - 7 * √2) / (100 - 49 * 2) := by rw [←(sqrt_mul zero_le_two), sqrt_mul_self zero_le_two]
      _ = (-3 - 3 * √2) * (7 - 5 * √2) / (-1) + (4 + 4 * √2) * (10 - 7 * √2) / 2 := by ring_nf
      _ = (3 + 3 * √2) * (7 - 5 * √2) + (2 + 2 * √2) * (10 - 7 * √2) := by ring_nf
      _ = 21 + 6 * √2 - 15 * (√2 * √2) + 20 + 6 * √2 - 14 * (√2 * √2) := by ring_nf
      _ = 41 + 12 * √2 - 29 * (√2 * √2) := by ring_nf
      _ = 41 + 12 * √2 - 29 * 2 := by rw [←(sqrt_mul zero_le_two), sqrt_mul_self zero_le_two]
      _ = -17 + 12 * √2 := by ring_nf
    
    use (1 : ℝ), (1 + √2), (4 + 3 * √2) -- We choose a simple value to prove that the value is in the set
    have qpos : 0 < 1 + √2 := by positivity
    have rpos : 0 < 4 + 3 * √2 := by positivity

    have hpq : (1 + √2) = (1 + √2) * 1 := by simp
    have hpr : (4 + 3 * √2) = (4 + 3 * √2) * 1 := by simp
        
    constructor
    exact one_pos
    constructor
    exact qpos
    constructor
    exact rpos

    rw [abc_min (1 : ℝ) (1 + √2) (4 + 3 * √2) one_pos qpos rpos hpq hpr]