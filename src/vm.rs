use crate::ast::{Name, Code, Statement, Expr, Binop};
use std::cmp::Ordering;
use std::collections::HashMap;


struct CallFrame {
    pub names: HashMap<Name, Value>,
}

impl CallFrame {
    pub fn new() -> CallFrame {
        CallFrame { names: HashMap::new() }
    }
}


pub struct VM {
    call_stack: Vec<CallFrame>,
    namespace_stack: Vec<Name>,
}


impl VM {
    pub fn new() -> VM {
        VM { call_stack: vec![CallFrame::new()], namespace_stack: Vec::new() }
    }

    pub fn assign(&mut self, name: Name, value: Value) {
        self
            .call_stack
            .last_mut()
            .expect("Internal error: call stack is empty")
            .names
            .insert(name, value);
    }

    pub fn get(&self, name: &Name) -> Option<Value> {
        for call_frame in self.call_stack.iter().rev() {
            if let Some(value) = call_frame.names.get(name) {
                return Some(value.clone());
            }
        }
        None
    }

    pub fn enter_namespace(&mut self, name: Name) {
        self.namespace_stack.push(name);
    }

    pub fn leave_namespace(&mut self) {
        self
            .namespace_stack
            .pop()
            .expect("Internal error: namespace stack is empty when leaving a namespace");
    }

    pub fn call(&mut self, func: &Function, arguments: Vec<Value>) -> ExecResult<Value> {
        self.push_frame();
        for (param, value) in func.parameters.iter().cloned().zip(arguments.into_iter()) {
            self.assign(param, value);
        }
        let result = func.code.execute(self);
        self.pop_frame();
        result
    }

    fn push_frame(&mut self) {
        self.call_stack.push(CallFrame::new());
    }

    fn pop_frame(&mut self) {
        self
            .call_stack
            .pop()
            .expect("Internal error: call stack is empty when leaving a function");
    }
}


pub trait Execute {
    fn execute(&self, vm: &mut VM) -> ExecResult<Value>;
}

impl Execute for Statement {
    fn execute(&self, vm: &mut VM) -> ExecResult<Value> {
        use Statement::*;
        match self {
            NamespaceDef { name, body } => {
                vm.enter_namespace(name.clone());
                body.execute(vm)?;
                vm.leave_namespace();
                Ok(Value::Hashable(HashableValue::Nothing))
            },
            FunctionDef { name, parameters, body } => {
                vm.assign(
                    name.clone(),
                    Value::Unhashable(
                        UnhashableValue::Function(
                            Function {
                                parameters: parameters.clone(),
                                code: body.clone(),
                            }
                        )
                    )
                );
                Ok(Value::Hashable(HashableValue::Nothing))
            },
            Assignment { target, expr } => {
                let value = expr.evaluate(vm)?;
                vm.assign(target.clone(), value);
                Ok(Value::Hashable(HashableValue::Nothing))
            },
            Expression(expr) => expr.evaluate(vm),
        }
    }
}

impl Execute for Code {
    fn execute(&self, vm: &mut VM) -> ExecResult<Value> {
        for statement in self.as_vec().iter() {
            // TODO: handle return statements
            statement.execute(vm)?;
        }
        Ok(Value::Hashable(HashableValue::Nothing))
    }
}


#[derive(Clone)]
pub struct Function {
    pub parameters: Vec<Name>,
    pub code: Code,
}


impl PartialEq for Function {
    fn eq(&self, _: &Function) -> bool {
        false
    }
}


#[derive(PartialEq, Eq, Hash, Clone)]
pub enum HashableValue {
    Bool(bool),
    Int(i64),
    String(String),
    Char(char),
    Nothing,
}

#[derive(PartialEq, Clone)]
pub enum UnhashableValue {
    List(Vec<Value>),
    Map(HashMap<HashableValue, Value>),
    Function(Function),
}

#[derive(PartialEq, Clone)]
pub enum Value {
    Hashable(HashableValue),
    Unhashable(UnhashableValue),
}

// BEGIN AWFUL CODE

impl HashableValue { 
    pub fn as_bool(&self) -> ExecResult<bool> {
        if let HashableValue::Bool(x) = self {
            Ok(*x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as Bool", self.typename())))
        }
    }
    
    pub fn as_int(&self) -> ExecResult<i64> {
        if let HashableValue::Int(x) = self {
            Ok(*x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as Int", self.typename())))
        }
    }
    
    pub fn as_string(&self) -> ExecResult<&String> {
        if let HashableValue::String(x) = self {
            Ok(x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as String", self.typename())))
        }
    }
    
    pub fn as_char(&self) -> ExecResult<char> {
        if let HashableValue::Char(x) = self {
            Ok(*x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as Char", self.typename())))
        }
    }

    pub fn as_nothing(&self) -> ExecResult<()> {
        if let HashableValue::Nothing = self {
            Ok(())
        } else {
            Err(ScriptError(format!("Cannot represent {} as Nothing", self.typename())))
        }
    }
}


impl UnhashableValue {
    pub fn as_list(&self) -> ExecResult<&Vec<Value>> {
        if let UnhashableValue::List(x) = self {
            Ok(x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as List", self.typename())))
        }
    }

    pub fn as_map(&self) -> ExecResult<&HashMap<HashableValue, Value>> {
        if let UnhashableValue::Map(x) = self {
            Ok(x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as Map", self.typename())))
        }
    }

    pub fn as_function(&self) -> ExecResult<&Function> {
        if let UnhashableValue::Function(x) = self {
            Ok(x)
        } else {
            Err(ScriptError(format!("Cannot represent {} as Function", self.typename())))
        }
    }
}


impl Value {
    pub fn as_bool(&self) -> ExecResult<bool> {
        if let Value::Hashable(x) = self {
            x.as_bool()
        } else {
            Err(ScriptError(format!("Cannot represent {} as Bool", self.typename())))
        }
    }

    pub fn as_int(&self) -> ExecResult<i64> {
        if let Value::Hashable(x) = self {
            x.as_int()
        } else {
            Err(ScriptError(format!("Cannot represent {} as Int", self.typename())))
        }
    }

    pub fn as_string(&self) -> ExecResult<&String> {
        if let Value::Hashable(x) = self {
            x.as_string()
        } else {
            Err(ScriptError(format!("Cannot represent {} as String", self.typename())))
        }
    }

    pub fn as_char(&self) -> ExecResult<char> {
        if let Value::Hashable(x) = self {
            x.as_char()
        } else {
            Err(ScriptError(format!("Cannot represent {} as Char", self.typename())))
        }
    }

    pub fn as_nothing(&self) -> ExecResult<()> {
        if let Value::Hashable(x) = self {
            x.as_nothing()
        } else {
            Err(ScriptError(format!("Cannot represent {} as Nothing", self.typename())))
        }
    }

    pub fn as_list(&self) -> ExecResult<&Vec<Value>> {
        if let Value::Unhashable(x) = self {
            x.as_list()
        } else {
            Err(ScriptError(format!("Cannot represent {} as List", self.typename())))
        }
    }

    pub fn as_map(&self) -> ExecResult<&HashMap<HashableValue, Value>> {
        if let Value::Unhashable(x) = self {
            x.as_map()
        } else {
            Err(ScriptError(format!("Cannot represent {} as Map", self.typename())))
        }
    }

    pub fn as_function(&self) -> ExecResult<&Function> {
        if let Value::Unhashable(x) = self {
            x.as_function()
        } else {
            Err(ScriptError(format!("Cannot represent {} as Function", self.typename())))
        }
    }
}

// END AWFUL CODE (just kidding)


impl PartialOrd for Value {
    fn partial_cmp(&self, rhs: &Value) -> Option<Ordering> {
        use Value::*;
        use HashableValue::*;
        use UnhashableValue::*;
        match (self, rhs) {
            (Hashable(Int(x)), Hashable(Int(y)))        => Some(x.cmp(y)),
            (Hashable(String(x)), Hashable(String(y)))  => Some(x.cmp(y)),
            (Hashable(Char(x)), Hashable(Char(y)))      => Some(x.cmp(y)),
            (Unhashable(List(x)), Unhashable(List(y)))  => x.partial_cmp(y),
            _ => None,
        }
    }
}

pub trait Typename {
    fn typename(&self) -> &'static str;
}

impl Typename for Value {
    fn typename(&self) -> &'static str {
        use Value::*;
        match self {
            Hashable(x) => x.typename(),
            Unhashable(x) => x.typename(),
        }
    }
}

impl Typename for HashableValue {
    fn typename(&self) -> &'static str {
        use HashableValue::*;
        match self {
            Bool(_) => "Bool",
            Int(_) => "Int",
            String(_) => "String",
            Char(_) => "Char",
            Nothing => "Nothing",
        }
    }
}

impl Typename for UnhashableValue {
    fn typename(&self) -> &'static str {
        use UnhashableValue::*;
        match self {
            List(_) => "List",
            Map(_) => "Map",
            Function { .. } => "Function",
        }
    }
}


pub struct ScriptError(String);

pub type ExecResult<T> = Result<T, ScriptError>;


mod operations {
    use std::cmp::Ordering;
    use super::{Value, HashableValue, UnhashableValue, ExecResult, ScriptError, VM, Typename};

    mod util {
        pub fn halfsat_i64_to_usize(num: i64) -> usize {
            if num < 0 {
                0
            } else {
                num as usize
            }
        }
    }

    pub fn eval_and(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        let lhs = lhs.as_bool()?;
        let rhs = rhs.as_bool()?;
        Ok(Value::Hashable(HashableValue::Bool(lhs && rhs)))
    }

    pub fn eval_or(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        let lhs = lhs.as_bool()?;
        let rhs = rhs.as_bool()?;
        Ok(Value::Hashable(HashableValue::Bool(lhs || rhs)))
    }

    pub fn eval_not(operand: &Value) -> ExecResult<Value> {
        let operand = operand.as_bool()?;
        Ok(Value::Hashable(HashableValue::Bool(!operand)))
    }

    fn are_values_equality_comparable(lhs: &Value, rhs: &Value) -> bool {
        use Value::*;
        use HashableValue::*;
        use UnhashableValue::*;
        match (lhs, rhs) {
            (Hashable(Bool(_)), Hashable(Bool(_))) => true,
            (Hashable(Int(_)), Hashable(Int(_))) => true,
            (Hashable(String(_)), Hashable(String(_))) => true,
            (Hashable(Char(_)), Hashable(Char(_))) => true,
            (Unhashable(List(_)), Unhashable(List(_))) => true,
            (Unhashable(Map(_)), Unhashable(Map(_))) => true,
            _ => false,
        }
    }

    pub fn eval_equals(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        if are_values_equality_comparable(lhs, rhs) {
            Ok(Value::Hashable(HashableValue::Bool(lhs == rhs)))
        } else {
            Err(
                ScriptError(
                    format!(
                        "Cannot compare {} and {} for equality",
                        lhs.typename(),
                        rhs.typename()
                    )
                )
            )
        }
    }

    fn eval_cmp(lhs: &Value, rhs: &Value) -> ExecResult<Ordering> {
        match lhs.partial_cmp(rhs) {
            Some(ord) => Ok(ord),
            None => Err(
                ScriptError(
                    format!(
                        "Cannot compare {} and {}",
                        lhs.typename(),
                        rhs.typename(),
                    )
                )
            ),
        }
    }

    pub fn eval_lt(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        Ok(
            Value::Hashable(
                HashableValue::Bool(
                    if let Ordering::Less = eval_cmp(lhs, rhs)? {
                        true
                    } else {
                        false
                    }
                )
            )
        )
    }

    pub fn eval_gt(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        Ok(
            Value::Hashable(
                HashableValue::Bool(
                    if let Ordering::Greater = eval_cmp(lhs, rhs)? {
                        true
                    } else {
                        false
                    }
                )
            )
        )
    }

    pub fn eval_add(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        use Value::*;
        use HashableValue::*;
        use UnhashableValue::*;
        match (lhs, rhs) {
            (Hashable(Int(x)), Hashable(Int(y))) => Ok(Hashable(Int(x + y))),
            (Hashable(String(x)), Hashable(String(y))) => Ok(Hashable(String(x.clone() + &y))),
            (Unhashable(List(x)), Unhashable(List(y))) => Ok(
                Unhashable(
                    List(
                        x.iter().cloned().chain(
                            y.iter().cloned()
                        ).collect()
                    )
                )
            ),
            _ => Err(
                ScriptError(
                    format!(
                        "Cannot add {} and {}",
                        lhs.typename(),
                        rhs.typename()
                    )
                )
            )
        }
    }

    pub fn eval_sub(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        let lhs = lhs.as_int()?;
        let rhs = rhs.as_int()?;
        Ok(Value::Hashable(HashableValue::Int(lhs + rhs)))
    }

    pub fn eval_mul(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        use Value::*;
        use HashableValue::*;
        use UnhashableValue::*;
        match (lhs, rhs) {
            (Hashable(Int(x)), Hashable(Int(y))) => Ok(Hashable(Int(x * y))),
            (Hashable(String(x)), Hashable(Int(y))) => Ok(
                Hashable(String(x.repeat(util::halfsat_i64_to_usize(*y))))
            ),
            (Unhashable(List(x)), Hashable(Int(y))) => Ok(
                Unhashable(
                    List(
                        x
                            .iter()
                            .cycle()
                            .cloned()
                            .take(util::halfsat_i64_to_usize(*y).saturating_mul(x.len()))
                            .collect()
                    )
                )
            ),
            _ => Err(
                ScriptError(
                    format!(
                        "Cannot multiply {} by {}",
                        lhs.typename(),
                        rhs.typename()
                    )
                )
            )
        }
    }

    pub fn eval_div(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        let lhs = lhs.as_int()?;
        let rhs = rhs.as_int()?;
        Ok(Value::Hashable(HashableValue::Int(lhs / rhs)))
    }

    pub fn eval_mod(lhs: &Value, rhs: &Value) -> ExecResult<Value> {
        let lhs = lhs.as_int()?;
        let rhs = rhs.as_int()?;
        Ok(Value::Hashable(HashableValue::Int(lhs % rhs)))
    }

    pub fn eval_call(callable: &Value, arguments: Vec<Value>, vm: &mut VM) -> ExecResult<Value> {
        let func = callable.as_function()?;
        if arguments.len() != func.parameters.len() {
            return Err(
                ScriptError(
                    format!(
                        "Invalid function call: expected {} argument(s), got {}",
                        func.parameters.len(),
                        arguments.len()
                    )
                )
            )
        }

        vm.call(func, arguments)
    }

    pub fn eval_trampoline(callable: &Value, vm: &mut VM) -> ExecResult<Value> {
        let mut callable = callable.clone();
        while let Ok(func) = callable.as_function() {
            if !func.parameters.is_empty() {
                break;
            }
            callable = vm.call(func, Vec::new())?;
        }
        Ok(callable)
    }
}


pub trait Evaluate {
    fn evaluate(&self, vm: &mut VM) -> ExecResult<Value>;
}

impl Evaluate for Expr {
    fn evaluate(&self, vm: &mut VM) -> ExecResult<Value> {
        use Expr::*;
        match self {
            And(Binop { lhs, rhs })         => operations::eval_and(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            Or(Binop { lhs, rhs })          => operations::eval_or(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            Not { operand }                 => operations::eval_not(&operand.evaluate(vm)?),

            Equals(Binop { lhs, rhs })      => operations::eval_equals(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            LessThan(Binop { lhs, rhs })    => operations::eval_lt(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            GreaterThan(Binop { lhs, rhs }) => operations::eval_gt(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),

            Add(Binop { lhs, rhs })         => operations::eval_add(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            Sub(Binop { lhs, rhs })         => operations::eval_sub(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            Mul(Binop { lhs, rhs })         => operations::eval_mul(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            Div(Binop { lhs, rhs })         => operations::eval_div(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),
            Mod(Binop { lhs, rhs })         => operations::eval_mod(&lhs.evaluate(vm)?, &rhs.evaluate(vm)?),

            Call { callable, arguments }    => operations::eval_call(
                &callable.evaluate(vm)?,
                {
                    let mut evaluated = Vec::with_capacity(arguments.len());
                    for x in arguments.iter() {
                        evaluated.push(x.evaluate(vm)?);
                    }
                    evaluated
                },
                vm
            ),
            Trampoline { expr }             => operations::eval_trampoline(&expr.evaluate(vm)?, vm),
            
            NamedValue { name }             => match vm.get(name) {
                Some(x) => Ok(x),
                None => Err(ScriptError(format!("No such variable or function: {}", name.as_string()))),
            },
            StringLiteral { value }         => Ok(Value::Hashable(HashableValue::String(value.clone()))),
            CharLiteral { value }           => Ok(Value::Hashable(HashableValue::Char(*value))),
            IntLiteral { value }            => Ok(Value::Hashable(HashableValue::Int(*value))),
            BoolLiteral { value }           => Ok(Value::Hashable(HashableValue::Bool(*value))),
        }
    }
}

// END AWFUL CODE (for real)
