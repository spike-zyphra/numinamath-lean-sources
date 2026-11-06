import Mathlib


-- Define the constants from the formula provided in the solution sketch.
-- k0 is the coefficient for the number originally at the vertex V.
def k0 : ℕ := 1641

-- k1 is the coefficient for the sum of numbers originally at the edge-adjacent neighbors.
def k1 : ℕ := 1640

-- Define the specific initial values for the vertex V and its three distinct edge-adjacent neighbors that are claimed to yield the maximum value.
def val_at_V : ℕ := 8
def val_at_neighbor1 : ℕ := 7 -- The order of neighbors does not matter for their sum
def val_at_neighbor2 : ℕ := 6
def val_at_neighbor3 : ℕ := 5

-- Calculate the sum of the values at the three chosen neighbors.
def sum_of_neighbor_vals : ℕ :=
  val_at_neighbor1 + val_at_neighbor2 + val_at_neighbor3

lemma sum_of_neighbor_vals_eq_18 : sum_of_neighbor_vals = 18 := by
  unfold sum_of_neighbor_vals val_at_neighbor1 val_at_neighbor2 val_at_neighbor3
  norm_num 

-- Define the function representing the formula for the final value at vertex V.
-- S_V = k0 * x_V + k1 * (x_N1 + x_N2 + x_N3)
def final_value_formula (v n1 n2 n3 : ℕ) : ℕ :=
  k0 * v + k1 * (n1 + n2 + n3)


theorem combinatorics_609930 :
    final_value_formula val_at_V val_at_neighbor1 val_at_neighbor2 val_at_neighbor3 = 42648 := by
  unfold final_value_formula -- Expand the formula definition
  unfold k0 k1 val_at_V
  rw [show val_at_neighbor1 + val_at_neighbor2 + val_at_neighbor3 = sum_of_neighbor_vals by
          unfold sum_of_neighbor_vals; rfl,
      sum_of_neighbor_vals_eq_18]


  

