class MyMul (α : Type) where
  mul : α → α → α

class MySemigroup (α : Type) extends MyMul α where
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

class MyMonoid (α : Type) extends MySemigroup α where
  one : α
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a


instance : MyMonoid Nat where
  mul := Nat.add
  assoc := Nat.add_assoc
  one := 0
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero

-- Instance synthesis lets Lean automatically find registered
-- typeclass instances required by a term.

example : MyMonoid Nat := inferInstance
example : MySemigroup Nat := inferInstance

#check inferInstance

structure MyMonoidHom (α β : Type)
   [MyMonoid α] [MyMonoid β] where
  toFun : α → β
  map_one : toFun (MyMonoid.one) = MyMonoid.one
  map_mul :
    ∀ a b,
      toFun (MyMul.mul a b) =
       MyMul.mul (toFun a) (toFun b)
