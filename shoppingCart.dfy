// Define a datatype for user IDs that supports equality
datatype UserId = MkUserId()

// Define a datatype for item IDs that supports equality
datatype ItemId = MkItemId()

// Concrete witnesses to demonstrate that UserId and ItemId are inhabited
const UserIdWitness: UserId := MkUserId()
const ItemIdWitness: ItemId := MkItemId()

// Define a type for quantities (must be positive)
type Quantity = x: int | x > 0 witness 1

// Define a type for prices in US dollars
type Price = x: real | x >= 0.0

// Define a record for an item in the shopping cart
datatype CartItem = CartItem(item: ItemId, quantity: Quantity, price: Price)

// Define a shopping cart as a map from users to their cart items
type ShoppingCart = map<UserId, seq<CartItem>>

// Define a method to add an item to the shopping cart
method AddItem(cart: ShoppingCart, user: UserId, item: ItemId, price: Price, quantity: Quantity)
  returns (newCart: ShoppingCart)
  ensures newCart == if user in cart then cart[user := AddOrUpdateItem(cart[user], item, price, quantity)] else cart[user := [CartItem(item, quantity, price)]]
{
  if user in cart {
    newCart := cart[user := AddOrUpdateItem(cart[user], item, price, quantity)];
  } else {
    newCart := cart[user := [CartItem(item, quantity, price)]];
  }
}

// Helper function to add or update an item in the cart
function AddOrUpdateItem(items: seq<CartItem>, item: ItemId, price: Price, quantity: Quantity): seq<CartItem>
  requires quantity > 0
  ensures |items| <= |AddOrUpdateItem(items, item, price, quantity)| <= |items| + 1
{
  if |items| == 0 then
    [CartItem(item, quantity, price)]
  else if items[0].item == item then
    [CartItem(item, items[0].quantity + quantity, price)] + items[1..]
  else
    [items[0]] + AddOrUpdateItem(items[1..], item, price, quantity)
}


// Define a method to delete an item from the shopping cart
method DeleteItem(cart: ShoppingCart, user: UserId, item: ItemId)
  returns (newCart: ShoppingCart)
  ensures newCart == if user in cart then cart[user := RemoveItem(cart[user], item)] else cart
{
  if user in cart {
    newCart := cart[user := RemoveItem(cart[user], item)];
  } else {
    newCart := cart;
  }
}

// Helper function to remove an item from the cart
function RemoveItem(items: seq<CartItem>, item: ItemId): seq<CartItem>
  ensures |RemoveItem(items, item)| <= |items|
{
  if |items| == 0 then
    []
  else if items[0].item == item then
    items[1..]
  else
    [items[0]] + RemoveItem(items[1..], item)
}

// Define a method to change the quantity of an item in the shopping cart
method ChangeQuantity(cart: ShoppingCart, user: UserId, item: ItemId, newQuantity: Quantity)
  returns (newCart: ShoppingCart)
  ensures newCart == if user in cart then cart[user := UpdateQuantity(cart[user], item, newQuantity)] else cart
{
  if user in cart {
    newCart := cart[user := UpdateQuantity(cart[user], item, newQuantity)];
  } else {
    newCart := cart;
  }
}

// Helper function to update the quantity of an item in the cart
function UpdateQuantity(items: seq<CartItem>, item: ItemId, newQuantity: Quantity): seq<CartItem>
  ensures |UpdateQuantity(items, item, newQuantity)| == |items|
{
  if |items| == 0 then
    []
  else if items[0].item == item then
    [CartItem(item, newQuantity, items[0].price)] + items[1..]
  else
    [items[0]] + UpdateQuantity(items[1..], item, newQuantity)
}

// Define a method to query the total cost of the shopping cart
method TotalCost(cart: ShoppingCart, user: UserId) returns (total: Price)
  ensures total == if user in cart then CalculateTotal(cart[user]) else 0.0
{
  if user in cart {
    total := CalculateTotal(cart[user]);
  } else {
    total := 0.0;
  }
}

// Helper function to calculate the total cost of the cart
function CalculateTotal(items: seq<CartItem>): Price
{
  if |items| == 0 then
    0.0
  else
    items[0].price * items[0].quantity as real + CalculateTotal(items[1..])
}

// Define a method to proceed to checkout
method Checkout(cart: ShoppingCart, user: UserId) returns (checkoutCart: seq<CartItem>)
  ensures checkoutCart == if user in cart then cart[user] else []
{
  if user in cart {
    checkoutCart := cart[user];
  } else {
    checkoutCart := [];
  }
}