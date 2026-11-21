macro "nat_ring" : tactic => `(tactic| first
  | omega
  | (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega)
  | (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at * <;> omega))

macro "int_ring" : tactic => `(tactic| first
  | omega
  | (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.neg_mul, Int.mul_neg, Int.sub_eq_add_neg] <;> omega)
  | (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.neg_mul, Int.mul_neg, Int.sub_eq_add_neg] at * <;> omega))

