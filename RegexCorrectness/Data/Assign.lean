set_option autoImplicit false

namespace Regex.Data

class Assign.{u, v, w} (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  assign : coll → idx → elem → coll

notation:max coll:max "[" i:70 " := " v:70 "]" => Assign.assign coll i v

end Regex.Data
