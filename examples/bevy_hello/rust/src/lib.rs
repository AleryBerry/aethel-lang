use core::ffi::c_void;
use ::bevy::prelude::*;

#[derive(Component)]
pub struct Person;

#[derive(Component)]
pub struct Name(pub String);

pub fn app_new() -> *mut c_void {
    Box::into_raw(Box::new(App::new())) as *mut c_void
}

pub fn add_startup_system(app: *mut c_void, sys: impl Fn() + Send + Sync + 'static) {
    let app = unsafe { &mut *(app as *mut App) };
    app.add_systems(Startup, move || sys());
}

pub fn spawn_person(app: *mut c_void, name: &str) {
    let app = unsafe { &mut *(app as *mut App) };
    app.world_mut().spawn((Person, Name(name.to_string())));
}

pub fn spawn_body(app: *mut c_void, pos: Position, vel: Velocity) {
    let app = unsafe { &mut *(app as *mut App) };
    app.world_mut().spawn((pos, vel));
}

pub fn add_person_query_system(app: *mut c_void, greet: impl Fn(&str) + Send + Sync + 'static) {
    let app = unsafe { &mut *(app as *mut App) };
    app.add_systems(Update, move |query: Query<&Name, With<Person>>| {
        for name in &query {
            greet(&name.0);
        }
    });
}

pub fn add_movement_system(
    app: *mut c_void,
    step: impl Fn(&mut Position, Velocity) + Send + Sync + 'static,
) {
    let app = unsafe { &mut *(app as *mut App) };
    app.add_systems(Update, move |mut query: Query<(&mut Position, &Velocity)>| {
        for (mut pos, vel) in &mut query {
            step(&mut *pos, *vel);
        }
    });
}

pub fn app_update(app: *mut c_void) {
    let app = unsafe { &mut *(app as *mut App) };
    app.update();
}

pub fn app_free(app: *mut c_void) {
    if !app.is_null() {
        unsafe { drop(Box::from_raw(app as *mut App)); }
    }
}

pub fn step_positions_soa(q: Transform2DQuery, vx: f32, vy: f32) {
    for i in 0..q.len {
        q.x[i] += vx;
        q.y[i] += vy;
    }
}
