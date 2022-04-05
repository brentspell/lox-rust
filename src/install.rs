// Copyright 2020 The Evcxr Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use anyhow::{anyhow, bail, Result};
use std::path::PathBuf;
use std::{env, fs};

const VERSION_TXT: &[u8] = "0.1.0".as_bytes();

pub(crate) fn install() -> Result<()> {
    let kernel_dir = get_kernel_dir()?;
    fs::create_dir_all(&kernel_dir)?;
    let current_exe_path = env::current_exe()?;
    let current_exe = current_exe_path
        .to_str()
        .ok_or_else(|| anyhow!("current exe path isn't valid UTF-8"))?;
    let kernel_json = object! {
        "argv" => array![current_exe, "--control_file", "{connection_file}"],
        "display_name" => "Lox",
        "language" => "lox",
        "interrupt_mode" => "message",
    };
    let kernel_json_filename = kernel_dir.join("kernel.json");
    println!("Writing {}", kernel_json_filename.to_string_lossy());
    kernel_json.write_pretty(&mut fs::File::create(kernel_json_filename)?, 2)?;
    println!("Installation complete");
    Ok(())
}

/// Checks if the current installation is out-of-date, by looking at what's in
/// version.txt. If it is out of date, then updates it.
pub(crate) fn update_if_necessary() -> Result<()> {
    let kernel_dir = get_kernel_dir()?;
    let installed_version = std::fs::read(kernel_dir.join("version.txt")).unwrap_or_default();
    if installed_version != VERSION_TXT {
        install()?;
        eprintln!(
            "\n\n==================================================================\n\
            Updated Lox Jupyter installation. Note, updates unfortunately \n\
            won't take effect until the next time you start jupyter notebook.\n\
            ==================================================================\n"
        );
    }
    Ok(())
}

pub(crate) fn uninstall() -> Result<()> {
    let kernel_dir = get_kernel_dir()?;
    println!("Deleting {}", kernel_dir.to_string_lossy());
    fs::remove_dir_all(kernel_dir)?;
    println!("Uninstall complete");
    Ok(())
}

// https://jupyter-client.readthedocs.io/en/latest/kernels.html
fn get_kernel_dir() -> Result<PathBuf> {
    let jupyter_dir = if let Ok(dir) = env::var("JUPYTER_PATH") {
        PathBuf::from(dir)
    } else if let Some(dir) = get_user_kernel_dir() {
        dir
    } else {
        bail!("Couldn't get XDG data directory");
    };
    Ok(jupyter_dir.join("kernels").join("lox"))
}

#[cfg(not(target_os = "macos"))]
fn get_user_kernel_dir() -> Option<PathBuf> {
    dirs::data_dir().map(|data_dir| data_dir.join("jupyter"))
}

#[cfg(target_os = "macos")]
fn get_user_kernel_dir() -> Option<PathBuf> {
    dirs::data_dir().and_then(|d| d.parent().map(|data_dir| data_dir.join("Jupyter")))
}
