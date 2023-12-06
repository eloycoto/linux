// SPDX-License-Identifier: GPL-2.0

//! Driver for the Onsemi Buck Converter NCV6336
//!
//! Datasheet: https://www.onsemi.com/pdf/datasheet/ncv6336bm-d.pdf

use kernel::{
    c_str, i2c, of,
    prelude::*,
    regmap,
    regulator::{
        driver::{Config, Desc, Driver, Registration, RegmapHelpers, Regulator, Status, Type},
        Mode,
    },
    sync::Arc,
};
use register::*;

kernel::module_i2c_id_table!(I2C_MOD_TABLE, NCV6336_I2C_ID_TABLE);
kernel::define_i2c_id_table! {NCV6336_I2C_ID_TABLE, (), [
    (i2c::DeviceId(b"ncv6336"), None),
]}

kernel::module_of_id_table!(OF_MOD_TABLE, NCV6336_OF_ID_TABLE);
kernel::define_of_id_table! {NCV6336_OF_ID_TABLE, (), [
    (of::DeviceId::Compatible(b"onnn,ncv6336"), None),
]}

kernel::module_i2c_driver! {
    type: Ncv6336,
    name: "ncv6336",
    author: "Fabien Parent <fabien.parent@linaro.org>",
    license: "GPL",
}

regmap::define_regmap_field_descs!(FIELD_DESCS, {
    {
        pid, 0x3, kernel::regmap::access::READ, {
            value => raw([7:0], ro),
        }
    }, {
        rid, 0x4, kernel::regmap::access::READ, {
            value => raw([7:0], ro),
        }
    }, {
        fid, 0x5, kernel::regmap::access::READ, {
            value => raw([7:0], ro),
        }
    }, {
        progvsel1, 0x10, kernel::regmap::access::RW, {
            voutvsel1 => raw([6:0], rw),
            envsel1   => bit(7, rw),
        }
    }, {
        progvsel0, 0x11, kernel::regmap::access::RW, {
            voutvsel0 => raw([6:0], rw),
            envsel0   => bit(7, rw),
        }
    }, {
        pgood, 0x12, kernel::regmap::access::RW, {
            dischg => bit(4, rw),
        }
    }, {
        command, 0x14, kernel::regmap::access::RW, {
            vselgt   => bit(0, rw),
            pwmvsel1 => bit(6, rw),
            pwmvsel0 => bit(7, rw),
        }
    }, {
        limconf, 0x16, kernel::regmap::access::RW, {
            rearm     => bit(0, rw),
            rststatus => bit(1, rw),
            tpwth     => enum([5:4], rw, {
                Temp83C  = 0x0,
                Temp94C  = 0x1,
                Temp105C = 0x2,
                Temp116C = 0x3,
            }),
            ipeak     => enum([7:6], rw, {
                Peak3p5A = 0x0,
                Peak4p0A = 0x1,
                Peak4p5A = 0x2,
                Peak5p0A = 0x3,
            }),
        }
    }
});

static NCV6336_DESC: Desc = Desc::new::<Ncv6336>(c_str!("ncv6336"), Type::Voltage)
    .with_owner(&THIS_MODULE)
    .with_active_discharge(
        pgood::addr(),
        pgood::dischg::mask(),
        pgood::dischg::mask(),
        0,
    )
    .with_csel(
        limconf::addr(),
        limconf::ipeak::mask(),
        &[3500000, 4000000, 4500000, 5000000],
    )
    .with_enable(
        progvsel0::addr(),
        progvsel0::envsel0::mask(),
        progvsel0::envsel0::mask(),
        0,
    )
    .with_linear_mapping(
        progvsel0::addr(),
        progvsel0::voutvsel0::mask(),
        600000,
        6250,
        128,
        0,
    );

type RegulatorData = kernel::device::Data<Registrations, (), ()>;

struct Registrations {
    fields: regmap::Fields<{ FIELD_DESCS.count() }>,
    regulator: Option<Registration>,
}

struct Ncv6336;
impl i2c::Driver for Ncv6336 {
    type Data = Arc<RegulatorData>;

    kernel::driver_i2c_id_table!(NCV6336_I2C_ID_TABLE);
    kernel::driver_of_id_table!(NCV6336_OF_ID_TABLE);

    fn probe(client: &mut i2c::Client) -> Result<Self::Data> {
        let config = regmap::Config::<AccessOps>::new(8, 8)
            .with_max_register(0x16)
            .with_cache_type(regmap::CacheType::RbTree);
        let regmap = Arc::try_new(regmap::Regmap::init_i2c(client, &config))?;
        let mut fields = regmap.alloc_fields(&FIELD_DESCS)?;
        let dev = client.device();

        let pid = pid::value::read(&mut fields)?;
        let rid = rid::value::read(&mut fields)?;
        let fid = fid::value::read(&mut fields)?;

        let data: Arc<RegulatorData> = kernel::new_device_data!(
            Registrations {
                fields,
                regulator: None
            },
            (),
            (),
            "Ncv6336::Registrations"
        )?
        .into();

        let config = Config::<Self::Data>::new(&dev)
            .with_drvdata(data.clone())
            .with_regmap(regmap.clone());

        let reg = Registration::register(&dev, &NCV6336_DESC, config)?;
        data.registrations().ok_or(EINVAL)?.regulator = Some(reg);

        dev_info!(dev, "PID: {pid:#x}, RID: {rid:#x}, FID: {fid:#x}");

        Ok(data)
    }
}

#[vtable]
impl Driver for Ncv6336 {
    type Data = Arc<RegulatorData>;

    fn list_voltage(reg: &Regulator, selector: u32) -> Result<i32> {
        reg.list_voltage_linear(selector)
    }

    fn enable(reg: &Regulator) -> Result {
        reg.enable_regmap()
    }

    fn disable(reg: &Regulator) -> Result {
        reg.disable_regmap()
    }

    fn is_enabled(reg: &Regulator) -> Result<bool> {
        reg.is_enabled_regmap()
    }

    fn set_active_discharge(reg: &Regulator, enable: bool) -> Result {
        reg.set_active_discharge_regmap(enable)
    }

    fn set_current_limit(reg: &Regulator, min_ua: i32, max_ua: i32) -> Result {
        reg.set_current_limit_regmap(min_ua, max_ua)
    }

    fn get_current_limit(reg: &Regulator) -> Result<i32> {
        reg.get_current_limit_regmap()
    }

    fn set_voltage_sel(reg: &Regulator, selector: u32) -> Result {
        reg.set_voltage_sel_regmap(selector)
    }

    fn get_voltage_sel(reg: &Regulator) -> Result<i32> {
        reg.get_voltage_sel_regmap()
    }

    fn set_mode(reg: &Regulator, mode: Mode) -> Result {
        let data = reg.data::<Self::Data>();
        let fields = &mut data.registrations().ok_or(EINVAL)?.fields;

        match mode {
            Mode::Normal => command::pwmvsel0::clear(fields),
            Mode::Fast => command::pwmvsel0::set(fields),
            _ => Err(ENOTSUPP),
        }
    }

    fn get_mode(reg: &Regulator) -> Mode {
        if let Some(mut registrations) = reg.data::<Self::Data>().registrations() {
            match command::pwmvsel0::is_set(&mut registrations.fields) {
                Ok(true) => Mode::Fast,
                Ok(false) => Mode::Normal,
                Err(_) => Mode::Invalid,
            }
        } else {
            Mode::Invalid
        }
    }

    fn get_status(reg: &Regulator) -> Result<Status> {
        if !Self::is_enabled(reg)? {
            return Ok(Status::Off);
        }

        Ok(Self::get_mode(reg).into())
    }

    fn set_suspend_voltage(reg: &Regulator, uv: i32) -> Result {
        let data = reg.data::<Self::Data>();
        let fields = &mut data.registrations().ok_or(EINVAL)?.fields;

        let quot = (uv - 600000) / 6250;
        let rem = (uv - 600000) % 6250;
        let selector = if rem > 0 { quot + 1 } else { quot };

        progvsel1::voutvsel1::write(fields, selector as _)
    }

    fn set_suspend_enable(reg: &Regulator) -> Result {
        let data = reg.data::<Self::Data>();
        let fields = &mut data.registrations().ok_or(EINVAL)?.fields;

        progvsel1::envsel1::set(fields)?;
        command::vselgt::clear(fields)
    }

    fn set_suspend_disable(reg: &Regulator) -> Result {
        let data = reg.data::<Self::Data>();
        let fields = &mut data.registrations().ok_or(EINVAL)?.fields;

        progvsel1::envsel1::clear(fields)?;
        command::vselgt::set(fields)
    }

    fn set_suspend_mode(reg: &Regulator, mode: Mode) -> Result {
        let data = reg.data::<Self::Data>();
        let fields = &mut data.registrations().ok_or(EINVAL)?.fields;

        match mode {
            Mode::Normal => command::pwmvsel1::clear(fields),
            Mode::Fast => command::pwmvsel1::set(fields),
            _ => Err(ENOTSUPP),
        }
    }
}
