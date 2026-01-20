

# Algorithm Loop invariants inference

## 1. Installation and Deployment

### 1.1 Conda Environment

We provide a complete package list for creating the required Conda environment.

To create the environment, simply run:

```
conda create --name <virtual_env_name> --file spec_list.txt
```

This command will automatically install all required dependencies.

### 1.2  Frama-C Installation

Frama-C needs to be installed separately.

We provide the installer for **Frama-C version 31.0**.
 For detailed installation instructions, please refer to the official guide:

> https://git.frama-c.com/pub/frama-c/blob/master/INSTALL.md

Follow the steps in the documentation to complete the installation on your system.

## 2. Getting Started

After completing the environment setup:

1. Enter the `src` directory:

   ```
   cd src
   ```

2. Run the loop invariant inference script:

   ```
   python loopinvinfer.py --file <FILE> --model <MODEL>
   ```

Where:

- `<FILE>` is the C source file for which you want to infer loop invariants.
- `<MODEL>` specifies the model name to be used for inference.

