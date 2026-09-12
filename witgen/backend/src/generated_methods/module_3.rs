use witgen_native::typed;

// method 0: "field.1.add.nat"
fn method_0(
    a0: typed::NatField<1>,
    a1: typed::NatField<1>,
) -> witgen_native::Result<typed::NatField<1>> {
    let v0: rug::Integer = (a0.clone()).0;
    let v1: rug::Integer = (a1.clone()).0;
    let v2: rug::Integer = v0.clone() + v1.clone();
    let v3: rug::Integer = v2.clone()
        % rug::Integer::from_str_radix(
            "115792089237316195423570985008687907853269984665640564039457584007908834671663",
            10,
        )?;
    let v4: typed::NatField<1> = typed::NatField::<1>(v3.clone());
    Ok(v4.clone())
}

// method 1: "field.1.mul.nat"
fn method_1(
    a0: typed::NatField<1>,
    a1: typed::NatField<1>,
) -> witgen_native::Result<typed::NatField<1>> {
    let v5: rug::Integer = (a0.clone()).0;
    let v6: rug::Integer = (a1.clone()).0;
    let v7: rug::Integer = v5.clone() * v6.clone();
    let v8: rug::Integer = v7.clone()
        % rug::Integer::from_str_radix(
            "115792089237316195423570985008687907853269984665640564039457584007908834671663",
            10,
        )?;
    let v9: typed::NatField<1> = typed::NatField::<1>(v8.clone());
    Ok(v9.clone())
}

// method 2: "field.1.square.nat"
fn method_2(a0: typed::NatField<1>) -> witgen_native::Result<typed::NatField<1>> {
    let v10: typed::NatField<1> = method_1(a0.clone(), a0.clone())?;
    Ok(v10.clone())
}

// program: "field_1_nat_methods"
pub fn run(
    a0: typed::NatField<1>,
    a1: typed::NatField<1>,
) -> witgen_native::Result<typed::NatField<1>> {
    let v11: typed::NatField<1> = method_2(a0.clone())?;
    let v12: typed::NatField<1> = method_1(v11.clone(), a1.clone())?;
    let v13: typed::NatField<1> = typed::NatField::<1>(
        rug::Integer::from_str_radix("5", 10)?
            % rug::Integer::from_str_radix(
                "115792089237316195423570985008687907853269984665640564039457584007908834671663",
                10,
            )?,
    );
    let v14: typed::NatField<1> = method_0(v12.clone(), v13.clone())?;
    Ok(v14.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::NatField<1>> {
    Ok(typed::parse_nat_field::<1>(value)?)
}

fn encode_0(value: typed::NatField<1>) -> serde_json::Value {
    serde_json::Value::String(value.0.to_string())
}

pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run(decode_0(&inputs[0])?, decode_0(&inputs[1])?)?))
}
