use eyre::Result;
use std::{cell::RefCell, fmt::Debug, rc::Rc};

/// A type that represents an empty state.
#[derive(Default)]
pub struct Empty;

/// A type that represents a graph filled.
#[derive(Default)]
pub struct Filled;

/// A builder that will be used to create a computational graph.
#[derive(Default, Debug)]
pub struct Builder<T = Empty> {
    /// Holds a reference with inner mutable state to the input values.
    /// This is used to fill in the values of the input nodes when
    /// [`Builder::fill_nodes`] is called.
    inputs: Vec<Rc<RefCell<Option<u32>>>>,
    /// Holds a list of nodes on which equality will be checked when
    /// [`Builder::check_constraints`] is called.
    assertions: Vec<(Node, Node)>,
    /// A marker type used to represent the state of the builder.
    _state: std::marker::PhantomData<T>,
}

/// A type defining a callable hint in the graph
type Hint = Rc<dyn Fn(u32) -> u32>;

/// A node in the computational graph.
#[derive(Clone)]
pub enum Node {
    /// A sum of 2 nodes.
    Sum(Rc<Node>, Rc<Node>),
    /// A multiplication of 2 nodes.
    Mul(Rc<Node>, Rc<Node>),
    /// A constant value.
    Constant(u32),
    /// An input node with the index of the input.
    Input(Rc<RefCell<Option<u32>>>, u8),
    /// A hint that allows you to perform operations that are not supported by the graph
    /// (e.g. division, square root).
    Hint(Hint, Rc<Node>),
}

impl Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Sum(a, b) => write!(f, "{:?} + {:?}", a, b),
            Node::Mul(a, b) => write!(f, "{:?} * {:?}", a, b),
            Node::Input(_, index) => write!(f, "input_{index}"),
            Node::Constant(i) => write!(f, "{}", i),
            Node::Hint(_, a) => write!(f, "f({:?})", a),
        }
    }
}

impl Node {
    /// Evaluates the node by recursively evaluating its children.
    ///
    /// # Panics
    ///
    /// Panics if the input nodes haven't been filled.
    fn eval(&self) -> u32 {
        match self {
            Node::Sum(a, b) => a.eval() + b.eval(),
            Node::Mul(a, b) => a.eval() * b.eval(),
            Node::Input(i, _) => i.borrow().unwrap(),
            Node::Constant(i) => *i,
            Node::Hint(hint, a) => hint(a.eval()),
        }
    }
}

impl Builder<Empty> {
    /// Initializes a node in the graph.
    pub fn init(&mut self) -> Node {
        tracing::info!("Creating a new input node: input_{}", self.inputs.len());

        let input_node = Rc::new(RefCell::new(None));
        self.inputs.push(input_node.clone());
        Node::Input(input_node, self.inputs.len() as u8 - 1)
    }

    /// Initializes a node in a graph, set to a constant value.
    pub fn constant(&mut self, value: u32) -> Node {
        tracing::info!("Creating a new constant node {}", value);

        Node::Constant(value)
    }

    /// Adds 2 nodes in the graph, returning a new node.
    pub fn add(&mut self, a: Node, b: Node) -> Node {
        tracing::info!("Adding nodes {:?} and {:?}", a, b);

        Node::Sum(a.into(), b.into())
    }

    /// Multiplies 2 nodes in the graph, returning a new node.
    pub fn mul(&mut self, a: Node, b: Node) -> Node {
        tracing::info!("Multiplying nodes {:?} and {:?}", a, b);

        Node::Mul(a.into(), b.into())
    }

    /// Asserts that the 2 input nodes are equal when calling [`Builder::check_constraints`].
    pub fn assert_equal(&mut self, a: Node, b: Node) {
        tracing::info!("Adding assertion: {:?} == {:?}", a, b);

        self.assertions.push((a, b));
    }

    /// Fills in all the nodes of the graph based on some inputs.
    ///
    /// # Error
    ///
    /// Returns an error if the number of input values does not match the number of input nodes.
    pub fn fill_nodes(self, input_values: Vec<u32>) -> Result<Builder<Filled>> {
        tracing::info!("Filling the input nodes of the graph");

        // Check if the number of input values is the same as the number of input nodes.
        if input_values.len() != self.inputs.len() {
            return Err(eyre::eyre!(
                "Number of input values does not match the number of input nodes"
            ));
        }

        for (input, value) in self.inputs.iter().zip(input_values.iter()) {
            *input.borrow_mut() = Some(*value);
        }

        Ok(Builder {
            inputs: self.inputs,
            assertions: self.assertions,
            _state: std::marker::PhantomData,
        })
    }

    /// An API for hinting values that allows you to perform operations
    /// like division or computing square roots.
    pub fn hint(&mut self, node: Node, hint: impl Fn(u32) -> u32 + 'static) -> Node {
        tracing::info!("Hinting node {:?} with function", node);

        Node::Hint(Rc::new(hint), node.into())
    }
}

impl Builder<Filled> {
    /// Given a graph that has `fill_nodes` already called on it
    /// checks that all the constraints hold.
    pub fn check_constraints(&mut self) -> bool {
        tracing::info!("Asserting constraints");

        for (a, b) in self.assertions.iter() {
            tracing::info!("Asserting {:?} == {:?}", a, b);
            if a.eval() != b.eval() {
                tracing::error!("Assertion failed: {:?} != {:?}", a, b);
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing_subscriber::FmtSubscriber;

    fn setup() {
        let subscriber = FmtSubscriber::builder()
            .with_max_level(tracing::Level::INFO)
            .finish();
        let _ = tracing::subscriber::set_global_default(subscriber);
    }

    #[test]
    fn test_incorrect_input_values() {
        setup();

        let mut builder = Builder::default();
        let _ = builder.init();
        let _ = builder.init();

        let maybe_builder_filled = builder.fill_nodes(vec![2]);
        assert!(maybe_builder_filled.is_err());
    }

    #[test]
    fn test_simple_function() {
        setup();

        // Build the function f(x) = x^2 + 5 + x
        let mut builder = Builder::default();
        let x = builder.init();
        let x_squared = builder.mul(x.clone(), x.clone());
        let five = builder.constant(5);
        let x_squared_plus_5 = builder.add(x_squared, five);
        let y = builder.add(x_squared_plus_5, x);

        let mut builder_filled = builder.fill_nodes(vec![2]).unwrap();
        builder_filled.check_constraints();
        assert_eq!(y.eval(), 11);
    }

    #[test]
    fn test_divide_hint() {
        setup();

        // Build the function f(x) = x + 1 and g(x) = f(x) / 8
        // We will assert that g(x) * 8 == f(x)
        let mut builder = Builder::default();
        let a = builder.init();
        let one = builder.constant(1);
        let b = builder.add(a, one);

        let c = builder.hint(b.clone(), |v| v / 8);
        let eight = builder.constant(8);
        let c_times_8 = builder.mul(c.clone(), eight);
        builder.assert_equal(b, c_times_8);

        let mut builder_filled = builder.fill_nodes(vec![7]).unwrap();
        assert!(builder_filled.check_constraints());
        assert_eq!(c.eval(), 8 / 8);
    }

    #[test]
    fn test_failing_assert() {
        setup();

        // Build the function f(x) = x + 1 and g(x) = f(x) * 2
        // We will assert that g(x) * 8 == f(x), which will fail
        let mut builder = Builder::default();
        let a = builder.init();
        let one = builder.constant(1);
        let b = builder.add(a, one);

        let c = builder.hint(b.clone(), |v| v * 2);
        let eight = builder.constant(8);
        let c_times_8 = builder.mul(c, eight);
        builder.assert_equal(b, c_times_8);

        let mut builder_filled = builder.fill_nodes(vec![7]).unwrap();
        assert!(!builder_filled.check_constraints());
    }

    #[test]
    fn test_sqrt_hint() {
        setup();

        // Build the function f(x) = sqrt(x + 7) and g(x) = f(x) * f(x)
        // We will assert that g(x) == x + 7
        let mut builder = Builder::default();
        let x = builder.init();
        let seven = builder.constant(7);
        let x_plus_seven = builder.add(x, seven);

        let sqrt_x_plus_7 = builder.hint(x_plus_seven.clone(), |v| f64::sqrt(v as f64) as u32);
        let computed_sq = builder.mul(sqrt_x_plus_7.clone(), sqrt_x_plus_7);
        builder.assert_equal(computed_sq.clone(), x_plus_seven);

        let mut builder_filled = builder.fill_nodes(vec![2]).unwrap();
        assert!(builder_filled.check_constraints());
        assert_eq!(computed_sq.eval(), 9);
    }

    #[test]
    fn test_multiple_assertions() {
        setup();

        // Build the function f(x) = x + 7 and g(x) = f(x) * f(x)
        // We will assert that g(x) == x + 7 and f(x) == 9
        let mut builder = Builder::default();
        let x = builder.init();
        let seven = builder.constant(7);
        let x_plus_seven = builder.add(x, seven);
        let nine = builder.constant(9);
        builder.assert_equal(nine, x_plus_seven.clone());

        let sqrt_x_plus_7 = builder.hint(x_plus_seven.clone(), |v| f64::sqrt(v as f64) as u32);
        let computed_sq = builder.mul(sqrt_x_plus_7.clone(), sqrt_x_plus_7);
        builder.assert_equal(computed_sq, x_plus_seven);

        let mut builder_filled = builder.fill_nodes(vec![2]).unwrap();
        assert!(builder_filled.check_constraints());
    }

    #[test]
    fn test_multiple_inputs() {
        setup();

        // Build the function f(x, y) = sqrt(x + y) and g(x, y) = f(x, y) * f(x, y)
        // We will assert that g(x, y) == x + y
        let mut builder = Builder::default();
        let x = builder.init();
        let y = builder.init();

        let x_plus_y = builder.add(x.clone(), y.clone());
        let sqrt_x_plus_y = builder.hint(x_plus_y.clone(), |v| f64::sqrt(v as f64) as u32);
        let computed_sq = builder.mul(sqrt_x_plus_y.clone(), sqrt_x_plus_y.clone());
        builder.assert_equal(computed_sq.clone(), x_plus_y);

        let mut builder_filled = builder.fill_nodes(vec![7, 2]).unwrap();

        assert!(builder_filled.check_constraints());
        assert_eq!(sqrt_x_plus_y.eval(), 3);
    }
}
