# L++ Schema Migration Rules

This directory contains JSON-based migration rule definitions for custom migrations.

## Migration File Format

Each migration file is a JSON document with the following structure:

```json
{
  "from_version": "lpp/vX.Y.Z",
  "to_version": "lpp/vA.B.C",
  "description": "Brief description of the migration",
  "changes": [
    {
      "type": "change_type",
      "...": "change-specific fields"
    }
  ],
  "notes": [
    "Optional notes about the migration"
  ]
}
```

## Supported Change Types

### 1. rename_field
Rename a field in the blueprint.

```json
{
  "type": "rename_field",
  "path": "transitions[*]",
  "from": "old_name",
  "to": "new_name",
  "transform": "wrap_array"
}
```

- `path`: JSON path to the field (use `[*]` for array iteration)
- `from`: Original field name
- `to`: New field name
- `transform`: Optional transformation (`wrap_array`, etc.)

### 2. add_field
Add a new field with a default value.

```json
{
  "type": "add_field",
  "path": "",
  "field": "new_field",
  "default": {},
  "condition": "missing"
}
```

- `path`: Path to parent object (empty string for root)
- `field`: Name of field to add
- `default`: Default value
- `condition`: When to add (`missing`, `always`)

### 3. remove_field
Remove a deprecated field.

```json
{
  "type": "remove_field",
  "path": "",
  "field": "deprecated_field",
  "condition": "exists"
}
```

- `path`: Path to parent object
- `field`: Name of field to remove
- `condition`: When to remove (`exists`, `always`)

### 4. convert_type
Convert a field's value type.

```json
{
  "type": "convert_type",
  "path": "terminal_states",
  "from": "string",
  "to": "array",
  "transform": "string_to_array"
}
```

- `path`: Path to the field
- `from`: Original type
- `to`: Target type
- `transform`: Conversion function (`string_to_array`, `array_to_string`, `wrap_object`, `unwrap_object`)

### 5. move_field
Move a field to a different location.

```json
{
  "type": "move_field",
  "from_path": "old.path.field",
  "to_path": "new.path.field"
}
```

### 6. transform_value
Apply a transformation to a field's value.

```json
{
  "type": "transform_value",
  "path": "some.field",
  "function": "uppercase"
}
```

- `function`: Transformation function (`uppercase`, `lowercase`, `snake_case`)

## Built-in Migrations

The Schema Migrator includes built-in migrations for:

- `lpp/v0.1.0` -> `lpp/v0.1.1`
- `lpp/v0.1.1` -> `lpp/v0.1.2`

Custom migrations in this directory will be automatically discovered and used.

## Creating Custom Migrations

1. Create a JSON file in this directory
2. Name it descriptively (e.g., `v0.1.2_to_v0.2.0.json`)
3. Define the migration following the format above
4. Test using the migrator's dry run mode

## Example Usage

```bash
# Preview migration
python interactive.py my_blueprint.json --preview

# Apply migration
python interactive.py my_blueprint.json --migrate
```
