// Instance methods: query methods read the object's fields; mutators are skipped.

class Account {
  var balance: int
  var limit: nat

  ghost predicate Valid()
    reads this
  {
    balance + limit >= 0
  }

  constructor (b: int, l: nat)
    requires b + l >= 0
    ensures Valid() && balance == b && limit == l
  {
    balance := b;
    limit := l;
  }

  // determined: reads a field, result fully specified
  method Available() returns (a: int)
    requires Valid()
    ensures a == balance + limit
  {
    a := balance + limit;
  }

  // not determined: only a lower bound (no witness search for instance methods yet)
  method WeakAvailable() returns (a: int)
    requires Valid()
    ensures a >= 0
  {
    a := balance + limit;
  }

  // skipped: mutator, its contract is about the state before and after
  method Deposit(x: nat) returns (newBalance: int)
    requires Valid()
    modifies this
    ensures Valid() && balance == old(balance) + x && newBalance == balance
  {
    balance := balance + x;
    newBalance := balance;
  }
}

trait Shape {
  // determined: abstract method in a trait, the contract alone pins the result
  method Doubled(x: int) returns (y: int)
    ensures y == 2 * x
}

datatype Point = Point(x: int, y: int) {
  // determined: member method of a datatype value
  method Sum() returns (s: int)
    ensures s == x + y
  {
    s := x + y;
  }

  // not determined
  method AnyAbove() returns (s: int)
    ensures s > x
  {
    s := x + 1;
  }
}
