mod legacy;
mod options;

use oxc_allocator::CloneIn;
use oxc_ast::{NONE, ast::*};
use oxc_span::SPAN;
use oxc_traverse::Traverse;

use crate::{
    context::TraverseCtx,
    state::TransformState,
    utils::ast_builder::create_accessor_method,
};

use legacy::LegacyDecorator;
pub use options::DecoratorOptions;

pub struct Decorator<'a> {
    options: DecoratorOptions,

    // Plugins
    legacy_decorator: LegacyDecorator<'a>,
}

impl Decorator<'_> {
    pub fn new(options: DecoratorOptions) -> Self {
        Self { legacy_decorator: LegacyDecorator::new(options.emit_decorator_metadata), options }
    }
}

impl<'a> Traverse<'a, TransformState<'a>> for Decorator<'a> {
    #[inline]
    fn exit_program(
        &mut self,
        node: &mut Program<'a>,
        ctx: &mut oxc_traverse::TraverseCtx<'a, TransformState<'a>>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.exit_program(node, ctx);
        }
    }

    #[inline]
    fn enter_statement(&mut self, stmt: &mut Statement<'a>, ctx: &mut TraverseCtx<'a>) {
        if self.options.legacy {
            self.legacy_decorator.enter_statement(stmt, ctx);
        }
    }

    #[inline]
    fn exit_statement(&mut self, stmt: &mut Statement<'a>, ctx: &mut TraverseCtx<'a>) {
        if self.options.legacy {
            self.legacy_decorator.exit_statement(stmt, ctx);
        }
    }

    #[inline]
    fn enter_class(&mut self, node: &mut Class<'a>, ctx: &mut TraverseCtx<'a>) {
        if self.options.legacy {
            // Lower `accessor` properties to private backing fields + get/set pairs.
            // Must run before `enter_class_body` so that es2022 class-properties can
            // transform the newly created private backing fields.
            Self::lower_accessor_properties(node, ctx);
            self.legacy_decorator.enter_class(node, ctx);
        }
    }

    #[inline]
    fn exit_class(&mut self, node: &mut Class<'a>, ctx: &mut TraverseCtx<'a>) {
        if self.options.legacy {
            self.legacy_decorator.exit_class(node, ctx);
        }
    }

    #[inline]
    fn enter_method_definition(
        &mut self,
        node: &mut MethodDefinition<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.enter_method_definition(node, ctx);
        }
    }

    #[inline]
    fn exit_method_definition(
        &mut self,
        node: &mut MethodDefinition<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.exit_method_definition(node, ctx);
        }
    }

    #[inline]
    fn enter_accessor_property(
        &mut self,
        node: &mut AccessorProperty<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.enter_accessor_property(node, ctx);
        }
    }

    #[inline]
    fn exit_accessor_property(
        &mut self,
        node: &mut AccessorProperty<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.exit_accessor_property(node, ctx);
        }
    }

    #[inline]
    fn enter_property_definition(
        &mut self,
        node: &mut PropertyDefinition<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.enter_property_definition(node, ctx);
        }
    }

    #[inline]
    fn exit_property_definition(
        &mut self,
        node: &mut PropertyDefinition<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.exit_property_definition(node, ctx);
        }
    }

    #[inline]
    fn enter_decorator(
        &mut self,
        node: &mut oxc_ast::ast::Decorator<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.options.legacy {
            self.legacy_decorator.enter_decorator(node, ctx);
        }
    }
}

impl<'a> Decorator<'a> {
    #[inline]
    pub fn exit_class_at_end(&mut self, class: &mut Class<'a>, ctx: &mut TraverseCtx<'a>) {
        if self.options.legacy {
            self.legacy_decorator.exit_class_at_end(class, ctx);
        }
    }

    /// Lower `accessor` properties to private backing fields + get/set pairs.
    ///
    /// `accessor prop: T = val` becomes:
    /// ```js
    /// #prop_accessor_storage = val;
    /// get prop() { return this.#prop_accessor_storage; }
    /// set prop(value) { this.#prop_accessor_storage = value; }
    /// ```
    fn lower_accessor_properties(class: &mut Class<'a>, ctx: &mut TraverseCtx<'a>) {
        if !class
            .body
            .body
            .iter()
            .any(|e| matches!(e, ClassElement::AccessorProperty(p) if !p.r#type.is_abstract()))
        {
            return;
        }

        let class_scope_id = class.scope_id();
        let mut new_body = ctx.ast.vec_with_capacity(class.body.body.len() * 3);

        for element in class.body.body.drain(..) {
            let ClassElement::AccessorProperty(accessor) = element else {
                new_body.push(element);
                continue;
            };
            if accessor.r#type.is_abstract() {
                new_body.push(ClassElement::AccessorProperty(accessor));
                continue;
            }

            let mut accessor = accessor.unbox();
            let is_static = accessor.r#static;
            let computed = accessor.computed;

            // Get the name for the backing field: `<name>_accessor_storage`
            let name = match &accessor.key {
                PropertyKey::StaticIdentifier(id) => &id.name,
                PropertyKey::PrivateIdentifier(id) => &id.name,
                _ => {
                    // Computed keys: fall back to keeping the accessor as-is
                    new_body.push(ClassElement::AccessorProperty(ctx.ast.alloc(accessor)));
                    continue;
                }
            };
            let storage_name = ctx.ast.atom(&format!("{name}_accessor_storage"));

            // Transfer decorators to the getter so legacy decorator transform can process them.
            let decorators = std::mem::replace(&mut accessor.decorators, ctx.ast.vec());

            let getter_key = accessor.key.clone_in(ctx.ast.allocator);
            let setter_key = accessor.key.clone_in(ctx.ast.allocator);

            // 1. Private backing field: `#<name>_accessor_storage = <value>`
            new_body.push(ctx.ast.class_element_property_definition(
                SPAN,
                PropertyDefinitionType::PropertyDefinition,
                ctx.ast.vec(),
                ctx.ast.property_key_private_identifier(SPAN, storage_name),
                NONE,
                accessor.value.take(),
                false,
                is_static,
                false,
                false,
                false,
                false,
                false,
                None,
            ));

            // 2. Getter: `get <name>() { return this.#<name>_accessor_storage; }`
            new_body.push(create_accessor_method(
                decorators,
                getter_key,
                MethodDefinitionKind::Get,
                computed,
                is_static,
                storage_name,
                class_scope_id,
                ctx,
            ));

            // 3. Setter: `set <name>(value) { this.#<name>_accessor_storage = value; }`
            new_body.push(create_accessor_method(
                ctx.ast.vec(),
                setter_key,
                MethodDefinitionKind::Set,
                computed,
                is_static,
                storage_name,
                class_scope_id,
                ctx,
            ));
        }

        class.body.body = new_body;
    }
}
